import socket
import struct
import time
import collections
import random
import sys
import threading
import concurrent.futures # Для параллельного разрешения

# --- Конфигурация The ASTRACAT DNS-R ---
LISTEN_IP = "0.0.0.0"
LISTEN_PORT = 5353
CACHE_TTL = 3600  # Максимальное время хранения записи в кэше по умолчанию (1 час)
MAX_CACHE_SIZE = 5000 # Максимальное количество записей в кэше (увеличено для лучшего кэширования)
QUERY_TIMEOUT = 1.5   # Таймаут для каждого исходящего DNS-запроса (немного уменьшен)
MAX_RECURSION_DEPTH = 15 # Ограничение глубины рекурсии

# Основные корневые DNS-серверы (по состоянию на 2025 год могут быть небольшие изменения, но эти стабильны)
ROOT_SERVERS = [
    "198.41.0.4",   # a.root-servers.net (Verisign)
    "199.9.14.201", # b.root-servers.net (ISI)
    "192.33.4.12",  # c.root-servers.net (Cogent)
    "199.7.91.13",  # d.root-servers.net (UMD)
    "192.203.230.10", # e.root-servers.net (NASA)
    "192.5.5.241",  # f.root-servers.net (ISC)
    "192.112.36.4", # g.root-servers.net (DoD)
    "198.97.190.53",# h.root-servers.net (Army Research Lab)
    "192.36.148.17",# i.root-servers.net (Autonomica)
    "192.58.128.30",# j.root-servers.net (Verisign)
    "193.0.14.129", # k.root-servers.net (RIPE NCC)
    "199.7.83.42",  # l.root-servers.net (ICANN)
    "202.12.27.33"  # m.root-servers.net (WIDE Project)
]

# --- Статистика ---
stats = {
    "total_queries": 0,
    "cache_hits": 0,
    "cache_misses": 0,
    "avg_recursion_depth": 0.0,
    "total_recursion_calls": 0, # Суммарная глубина для расчета среднего
    "errors": 0,
    "resolved_domains": collections.defaultdict(int), # Домены, которые были успешно разрешены
    "uptime_start": time.time()
}

# --- Кэш DNS-записей ---
# { (qname, qtype): { 'answers': [], 'ns': [], 'expiration': timestamp } }
dns_cache = collections.OrderedDict() # OrderedDict для FIFO кэша

# Для защиты доступа к кэшу и статистике
cache_lock = threading.Lock()
stats_lock = threading.Lock()

# Типы DNS-записей
TYPE_A = 1
TYPE_NS = 2
TYPE_CNAME = 5
TYPE_AAAA = 28
TYPE_PTR = 12 # Для реверсивных запросов (не реализовано в рекурсии, но полезно знать)

# Классы DNS-записей
CLASS_IN = 1 # Internet

# --- Вспомогательные функции для работы с DNS-пакетами ---
def encode_dns_name(domain):
    """Кодирует доменное имя для DNS-папакета."""
    parts = domain.split(".")
    encoded_name = b""
    for part in parts:
        if part:
            encoded_name += struct.pack("B", len(part)) + part.encode("ascii")
    encoded_name += b"\x00"
    return encoded_name

def decode_dns_name(data, offset):
    """Декодирует доменное имя из DNS-пакета, обрабатывая компрессию."""
    name_parts = []
    original_offset = offset # Для возврата к началу имени для следующей записи
    
    while True:
        length = data[offset]
        if (length & 0xC0) == 0xC0: # Указатель (compression)
            ptr_offset = struct.unpack(">H", data[offset:offset+2])[0] & 0x3FFF
            offset += 2 # Пропускаем 2 байта указателя
            name_parts.append(decode_dns_name(data, ptr_offset)[0]) # Рекурсивный вызов для разыменования указателя
            return ".".join(name_parts), original_offset + 2 # Возвращаем имя и смещение после указателя
        elif length == 0: # Конец имени
            offset += 1
            break
        else: # Метка (не сжатая часть)
            name_parts.append(data[offset + 1 : offset + 1 + length].decode("ascii"))
            offset += length + 1
    return ".".join(name_parts), offset

def build_dns_query_packet(qname, qtype, query_id):
    """Строит полный DNS-запрос."""
    flags = 0x0100 # Standard query, recursion desired
    qdcount = 1
    header = struct.pack(">HHHHHH", query_id, flags, qdcount, 0, 0, 0)
    encoded_qname = encode_dns_name(qname)
    question = encoded_qname + struct.pack(">HH", qtype, CLASS_IN)
    return header + question

def parse_dns_response_packet(data, original_qname, original_qtype_val):
    """Парсит DNS-ответ и извлекает записи."""
    
    # Заголовок (12 байт)
    # ID, Flags, QDCOUNT, ANCOUNT, NSCOUNT, ARCOUNT
    header_data = struct.unpack(">HHHHHH", data[0:12])
    query_id, flags, qdcount, ancount, nscount, arcount = header_data

    # Проверка RCODE (код ответа)
    rcode = flags & 0x0F
    if rcode != 0: # 0 = NoError, 3 = NXDOMAIN (Domain Not Found), 2 = ServFail
        # Для простоты, если есть RCODE != 0, считаем что не удалось разрешить
        return [], [], {'error': f"DNS RCODE: {rcode}"}
    
    # Секция вопросов
    offset = 12
    qname, qtype_val, qclass, offset = parse_dns_question_section(data, offset)

    answers = []
    authoritative_nameservers = [] # NS records
    additional_records = [] # A/AAAA records for NS (glue records)

    # Парсинг секции ответов, NS-записей и дополнительных записей
    for _ in range(ancount + nscount + arcount):
        start_record_offset = offset # Сохраняем начальное смещение записи
        record_name, offset = decode_dns_name(data, offset)
        
        # Читаем Type, Class, TTL, RDLENGTH
        r_type, r_class, r_ttl, r_data_len = struct.unpack(">HHIH", data[offset:offset+10])
        offset += 10
        r_data = data[offset : offset + r_data_len]
        offset += r_data_len

        record = {
            'name': record_name.strip('.'),
            'type': r_type,
            'class': r_class,
            'ttl': r_ttl,
            'value': None # Будет заполнено ниже
        }

        if r_type == TYPE_A:
            record['value'] = socket.inet_ntoa(r_data)
            if record['name'] == original_qname or record['name'] in [ns['name'] for ns in authoritative_nameservers]:
                answers.append(record)
            else:
                additional_records.append(record)
        elif r_type == TYPE_AAAA:
            record['value'] = socket.inet_ntop(socket.AF_INET6, r_data)
            if record['name'] == original_qname or record['name'] in [ns['name'] for ns in authoritative_nameservers]:
                answers.append(record)
            else:
                additional_records.append(record)
        elif r_type == TYPE_NS:
            ns_value, _ = decode_dns_name(r_data, 0)
            record['value'] = ns_value.strip('.')
            authoritative_nameservers.append(record)
        elif r_type == TYPE_CNAME:
            cname_value, _ = decode_dns_name(r_data, 0)
            record['value'] = cname_value.strip('.')
            answers.append(record)
        # TODO: Добавить поддержку других типов записей (MX, TXT, PTR и т.д.) по мере необходимости
    
    return answers, authoritative_nameservers, additional_records

# --- Вспомогательная функция для парсинга вопроса (отделена для чистоты) ---
def parse_dns_question_section(data, offset):
    """Парсит секцию вопросов DNS-пакета, возвращает qname, qtype, qclass и новое смещение."""
    qname, offset = decode_dns_name(data, offset)
    qtype = struct.unpack(">H", data[offset : offset + 2])[0]
    offset += 2
    qclass = struct.unpack(">H", data[offset : offset + 2])[0]
    offset += 2
    return qname, qtype, qclass, offset

# --- Ядро рекурсивного резолвера ---
def resolve_recursively(qname, qtype_val, current_ns_ips=None, depth=0):
    """
    Рекурсивно разрешает DNS-имя, начиная с корневых серверов или переданных NS-IP.
    Возвращает список ответов (A/AAAA/CNAME).
    """
    with stats_lock:
        stats["total_recursion_calls"] += 1
        stats["avg_recursion_depth"] = (stats["avg_recursion_depth"] * (stats["total_recursion_calls"] - 1) + depth) / stats["total_recursion_calls"] if stats["total_recursion_calls"] > 0 else depth

    if depth > MAX_RECURSION_DEPTH:
        # print(f"Превышена максимальная глубина рекурсии ({MAX_RECURSION_DEPTH}) для {qname}", file=sys.stderr)
        return []

    if current_ns_ips is None:
        current_ns_ips = list(ROOT_SERVERS) # Копия, чтобы не менять оригинал
        random.shuffle(current_ns_ips)

    for ns_ip in current_ns_ips:
        query_packet = build_dns_query_packet(qname, qtype_val, random.randint(0, 65535))
        response_packet = send_dns_query(ns_ip, query_packet)

        if response_packet:
            try:
                answers, authoritative_nameservers, additional_records = parse_dns_response_packet(response_packet, qname, qtype_val)

                # 1. Если есть прямые ответы для искомого домена (A, AAAA, CNAME)
                relevant_answers = [
                    a for a in answers 
                    if a['name'] == qname and (a['type'] == TYPE_A or a['type'] == TYPE_AAAA or a['type'] == TYPE_CNAME)
                ]
                if relevant_answers:
                    # Если CNAME, то нужно разрешить его
                    if any(a['type'] == TYPE_CNAME for a in relevant_answers):
                        cname_target = next(a['value'] for a in relevant_answers if a['type'] == TYPE_CNAME)
                        # Рекурсивно разрешаем CNAME
                        cname_resolved_answers = resolve_recursively(cname_target, qtype_val, None, depth + 1)
                        if cname_resolved_answers:
                            return relevant_answers + cname_resolved_answers
                        else:
                            # CNAME, но не удалось разрешить его цель
                            return relevant_answers 
                    else:
                        return relevant_answers # Нашли A/AAAA, возвращаем
                
                # 2. Если нет прямых ответов, но есть NS-записи (делегирование)
                if authoritative_nameservers:
                    next_ns_ips_to_try = []
                    for ns_record in authoritative_nameservers:
                        # Ищем glue records (A/AAAA записи для NS-серверов в секции additional)
                        glue_ips = [
                            ar['value'] for ar in additional_records
                            if ar['name'] == ns_record['value'] and (ar['type'] == TYPE_A or ar['type'] == TYPE_AAAA)
                        ]
                        if glue_ips:
                            next_ns_ips_to_try.extend(glue_ips)
                        else:
                            # Если нет glue records, нужно разрешить IP для NS-сервера
                            # Используем Executor для асинхронного разрешения NS-серверов
                            # для предотвращения блокировки основного потока рекурсии
                            try:
                                with concurrent.futures.ThreadPoolExecutor(max_workers=3) as executor:
                                    future = executor.submit(resolve_recursively, ns_record['value'], TYPE_A, None, depth + 1)
                                    resolved_glue = future.result(timeout=QUERY_TIMEOUT) # Таймаут на разрешение NS
                                    next_ns_ips_to_try.extend([r['value'] for r in resolved_glue if r['type'] == TYPE_A])
                            except (concurrent.futures.TimeoutError, Exception) as e:
                                # print(f"Не удалось разрешить NS {ns_record['value']} за таймаут: {e}", file=sys.stderr)
                                pass # Пробуем следующий NS
                                
                    next_ns_ips_to_try = list(set(next_ns_ips_to_try)) # Удалить дубликаты
                    if next_ns_ips_to_try:
                        # Рекурсивный вызов с новыми NS-серверами
                        return resolve_recursively(qname, qtype_val, next_ns_ips_to_try, depth + 1)
            
            except Exception as e:
                with stats_lock:
                    stats["errors"] += 1
                # print(f"Ошибка парсинга или обработки ответа от {ns_ip} для {qname}: {e}", file=sys.stderr)
                continue # Попробовать следующий NS-сервер
        else:
            with stats_lock:
                stats["errors"] += 1
            # print(f"Таймаут или ошибка соединения с {ns_ip} для {qname}", file=sys.stderr)
            continue # Попробовать следующий NS-сервер

    return [] # Не удалось разрешить

# --- Основной DNS-сервер ---
def dns_server_thread():
    sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    sock.bind((LISTEN_IP, LISTEN_PORT))
    print(f"The ASTRACAT DNS-R запущен на {LISTEN_IP}:{LISTEN_PORT}")
    print("Ожидание DNS-запросов...")

    with concurrent.futures.ThreadPoolExecutor(max_workers=50) as executor: # Пул для обработки входящих запросов
        while True:
            try:
                data, addr = sock.recvfrom(512)
                executor.submit(handle_dns_query, data, addr, sock)
            except KeyboardInterrupt:
                break
            except Exception as e:
                print(f"Ошибка в основном цикле DNS-сервера: {e}", file=sys.stderr)

def handle_dns_query(data, addr, sock):
    """Обрабатывает один входящий DNS-запрос в отдельном потоке."""
    try:
        query_id = struct.unpack(">H", data[0:2])[0]
        
        offset = 12
        qname, qtype_val, qclass, _ = parse_dns_question_section(data, offset)
        qname = qname.strip('.') # Убираем конечную точку

        with stats_lock:
            stats["total_queries"] += 1
        # print(f"\n[{time.strftime('%H:%M:%S')}] Получен запрос от {addr[0]} для {qname} (тип {qtype_val})")

        # Проверка кэша
        cache_key = (qname, qtype_val)
        cached_entry = None
        with cache_lock:
            if cache_key in dns_cache:
                cached_entry = dns_cache[cache_key]
                if time.time() >= cached_entry['expiration']:
                    # Запись в кэше устарела
                    del dns_cache[cache_key]
                    cached_entry = None # Обнуляем, чтобы пойти в рекурсию
                    # print(f"  Кэш-запись для {qname} устарела.")
        
        if cached_entry:
            # Кэш попадание
            with stats_lock:
                stats["cache_hits"] += 1
            # print(f"  Кэш-попадание для {qname}.")
            resolved_answers = cached_entry['answers']
            
            # Строим ответ из кэшированных данных
            response_header = build_dns_response_header(query_id, True, True, 0, len(resolved_answers), 0, 0)
            response_question = encode_dns_name(qname) + struct.pack(">HH", qtype_val, qclass)
            response_answers = build_answers_section(resolved_answers)
            full_response = response_header + response_question + response_answers
            sock.sendto(full_response, addr)
        else:
            # Кэш-промах, начинаем рекурсию
            with stats_lock:
                stats["cache_misses"] += 1
            # print(f"  Кэш-промах для {qname}. Начинаем рекурсию...")
            
            resolved_answers = resolve_recursively(qname, qtype_val)

            if resolved_answers:
                # Обновление статистики по разрешенным доменам
                with stats_lock:
                    stats["resolved_domains"][qname] += 1

                # Кэширование ответа
                min_ttl = min([a['ttl'] for a in resolved_answers]) if resolved_answers else CACHE_TTL
                with cache_lock:
                    dns_cache[cache_key] = {
                        'answers': resolved_answers,
                        'expiration': time.time() + min_ttl
                    }
                    while len(dns_cache) > MAX_CACHE_SIZE:
                        dns_cache.popitem(last=False) # Удаляем старейший элемент (FIFO)
                
                # Строим ответный пакет
                response_header = build_dns_response_header(query_id, True, True, 0, len(resolved_answers), 0, 0)
                response_question = encode_dns_name(qname) + struct.pack(">HH", qtype_val, qclass)
                response_answers = build_answers_section(resolved_answers)
                full_response = response_header + response_question + response_answers
                sock.sendto(full_response, addr)
            else:
                # Не удалось разрешить, отправляем SERVFAIL
                response_header = build_dns_response_header(query_id, True, False, 3, 0, 0, 0) # RCODE 3 = NXDOMAIN, 2 = SERVFAIL
                response_question = encode_dns_name(qname) + struct.pack(">HH", qtype_val, qclass)
                full_response = response_header + response_question
                sock.sendto(full_response, addr)

    except Exception as e:
        with stats_lock:
            stats["errors"] += 1
        print(f"Ошибка при обработке запроса от {addr}: {e}", file=sys.stderr)
        # Отправить SERVFAIL в ответ на ошибку
        try:
            error_response_header = build_dns_response_header(query_id, False, False, 2, 0, 0, 0) # RCODE 2 = ServFail
            sock.sendto(error_response_header, addr)
        except Exception:
            pass # Если даже тут ошибка, то просто пропускаем

def build_dns_response_header(query_id, authoritative_answer, recursion_available, rcode, ancount, nscount, arcount):
    """Строит заголовок DNS-ответа."""
    flags = 0x8000 # QR=1 (response)
    if authoritative_answer:
        flags |= 0x0400 # AA=1 (authoritative answer)
    if recursion_available:
        flags |= 0x0080 # RA=1 (recursion available)
    flags |= (rcode & 0x0F) # RCODE
    
    return struct.pack(">HHHHHH", query_id, flags, 1, ancount, nscount, arcount) # QDCOUNT всегда 1 для ответа на 1 вопрос

def build_answers_section(answers):
    """Строит секцию ответов DNS-пакета."""
    answer_section = b""
    for rec in answers:
        encoded_name = encode_dns_name(rec['name'])
        answer_section += encoded_name # Name (без компрессии для простоты)
        
        if rec['type'] == TYPE_A:
            answer_section += struct.pack(">HHIH", TYPE_A, CLASS_IN, rec['ttl'], 4) + socket.inet_aton(rec['value'])
        elif rec['type'] == TYPE_AAAA:
            answer_section += struct.pack(">HHIH", TYPE_AAAA, CLASS_IN, rec['ttl'], 16) + socket.inet_pton(socket.AF_INET6, rec['value'])
        elif rec['type'] == TYPE_CNAME:
            encoded_cname_value = encode_dns_name(rec['value'])
            answer_section += struct.pack(">HHIH", TYPE_CNAME, CLASS_IN, rec['ttl'], len(encoded_cname_value)) + encoded_cname_value
        # TODO: Добавить другие типы записей по мере необходимости
    return answer_section

def print_stats_thread():
    """Поток для периодического вывода статистики."""
    while True:
        try:
            time.sleep(30) # Выводить статистику каждые 30 секунд
            with stats_lock:
                uptime = time.time() - stats["uptime_start"]
                print(f"\n--- Статистика The ASTRACAT DNS-R (Uptime: {int(uptime // 3600)}h {int((uptime % 3600) // 60)}m {int(uptime % 60)}s) ---")
                for key, value in stats.items():
                    if key in ["total_queries", "cache_hits", "cache_misses", "errors"]:
                        print(f"  {key.replace('_', ' ').capitalize()}: {value}")
                print(f"  Процент попаданий в кэш: {stats['cache_hits'] / stats['total_queries'] * 100:.2f}%" if stats["total_queries"] > 0 else "  N/A")
                print(f"  Средняя глубина рекурсии: {stats['avg_recursion_depth']:.2f}" if stats["total_recursion_calls"] > 0 else "  N/A")
                if stats["resolved_domains"]:
                    print("  Разрешенные домены (топ 5):")
                    for domain, count in collections.Counter(stats["resolved_domains"]).most_common(5):
                        print(f"    - {domain}: {count} раз")
                print("---------------------------------------")
        except KeyboardInterrupt:
            break
        except Exception as e:
            print(f"Ошибка в потоке статистики: {e}", file=sys.stderr)


if __name__ == "__main__":
    try:
        # Запуск потока для вывода статистики
        stats_thread = threading.Thread(target=print_stats_thread, daemon=True)
        stats_thread.start()

        # Запуск основного DNS-сервера
        dns_server_thread()
    except KeyboardInterrupt:
        print("\nЗавершение работы The ASTRACAT DNS-R...")
        with stats_lock:
            print_stats_thread() # Выводим финальную статистику при выходе
    except Exception as e:
        print(f"Непредвиденная ошибка при запуске: {e}", file=sys.stderr)
