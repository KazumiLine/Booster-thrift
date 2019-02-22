from struct import pack, unpack
from io import BytesIO
from itertools import islice
from http import client as http_client
import sys, os, socket, warnings, base64, time, functools, itertools, operator, types, builtins, urllib
if sys.version_info[0] == 2:
    from cStringIO import StringIO as BufferIO
    def binary_to_str(bin_val):
        return bin_val
    def str_to_binary(str_val):
        return str_val
else:
    from io import BytesIO as BufferIO
    def binary_to_str(bin_val):
        return bin_val.decode('utf8',"ignore")
    def str_to_binary(str_val):
        return bytes(str_val, 'utf8',"ignore")


def make_helper(v_from, container):
    def helper(func):
        def nested(self, *args, **kwargs):
            assert self.state in (v_from, container), (self.state, v_from, container)
            return func(self, *args, **kwargs)
        return nested
    return helper
writer = make_helper(2, 3)
reader = make_helper(7, 6)

def makeZigZag(n, bits):
    checkIntegerLimits(n, bits)
    return (n << 1) ^ (n >> (bits - 1))

def fromZigZag(n):
    return (n >> 1) ^ -(n & 1)

def writeVarint(trans, n):
    out = bytearray()
    while True:
        if n & ~0x7f == 0:
            out.append(n)
            break
        else:
            out.append((n & 0xff) | 0x80)
            n = n >> 7
    trans.write(bytes(out))

def readVarint(trans):
    result = 0
    shift = 0
    while True:
        x = trans.readAll(1)
        byte = ord(x)
        result |= (byte & 0x7f) << shift
        if byte >> 7 == 0:
            return result
        shift += 7
        

class CompactType(object):
    STOP = 0x00
    TRUE = 0x01
    FALSE = 0x02
    BYTE = 0x03
    I16 = 0x04
    I32 = 0x05
    I64 = 0x06
    DOUBLE = 0x07
    BINARY = 0x08
    LIST = 0x09
    SET = 0x0A
    MAP = 0x0B
    STRUCT = 0x0C
    
class TType(object):
    STOP = 0
    VOID = 1
    BOOL = 2
    BYTE = 3
    I08 = 3
    DOUBLE = 4
    I16 = 6
    I32 = 8
    I64 = 10
    STRING = 11
    UTF7 = 11
    STRUCT = 12
    MAP = 13
    SET = 14
    LIST = 15
    UTF8 = 16
    UTF16 = 17

    _VALUES_TO_NAMES = (
        'STOP',
        'VOID',
        'BOOL',
        'BYTE',
        'DOUBLE',
        None,
        'I16',
        None,
        'I32',
        None,
        'I64',
        'STRING',
        'STRUCT',
        'MAP',
        'SET',
        'LIST',
        'UTF8',
        'UTF16',
    )


CTYPES = {
    TType.STOP: CompactType.STOP,
    TType.BOOL: CompactType.TRUE,  # used for collection
    TType.BYTE: CompactType.BYTE,
    TType.I16: CompactType.I16,
    TType.I32: CompactType.I32,
    TType.I64: CompactType.I64,
    TType.DOUBLE: CompactType.DOUBLE,
    TType.STRING: CompactType.BINARY,
    TType.STRUCT: CompactType.STRUCT,
    TType.LIST: CompactType.LIST,
    TType.SET: CompactType.SET,
    TType.MAP: CompactType.MAP,
}

TTYPES = {
    CompactType.STOP: TType.STOP,
    CompactType.TRUE: TType.BOOL,
    CompactType.BYTE: TType.BYTE,
    CompactType.I16: TType.I16,
    CompactType.I32: TType.I32,
    CompactType.I64: TType.I64,
    CompactType.DOUBLE: TType.DOUBLE,
    CompactType.BINARY: TType.STRING,
    CompactType.STRUCT: TType.STRUCT,
    CompactType.LIST: TType.LIST,
    CompactType.SET: TType.SET,
    CompactType.MAP: TType.MAP,
    CompactType.FALSE: TType.BOOL,
}

class Six(object):
    """Copyed By Benjamin Peterson"""
    def iterkeys(d, **kw):
        return iter(d.keys(**kw))
    def itervalues(d, **kw):
        return iter(d.values(**kw))
    def iteritems(d, **kw):
        return iter(d.items(**kw))


class TMessageType(object):
    CALL = 1
    REPLY = 2
    EXCEPTION = 3
    ONEWAY = 4

class TException(Exception):
    """Base class for all thrift exceptions."""

    # BaseException.message is deprecated in Python v[2.6,3.0)
    if (2, 6, 0) <= sys.version_info < (3, 0):
        def _get_message(self):
            return self._message

        def _set_message(self, message):
            self._message = message
        message = property(_get_message, _set_message)

    def __init__(self, message=None):
        Exception.__init__(self, message)
        self.message = message


class TApplicationException(TException):

    UNKNOWN = 0
    UNKNOWN_METHOD = 1
    INVALID_MESSAGE_TYPE = 2
    WRONG_METHOD_NAME = 3
    BAD_SEQUENCE_ID = 4
    MISSING_RESULT = 5
    INTERNAL_ERROR = 6
    PROTOCOL_ERROR = 7
    INVALID_TRANSFORM = 8
    INVALID_PROTOCOL = 9
    UNSUPPORTED_CLIENT_TYPE = 10

    def __init__(self, type=UNKNOWN, message=None):
        TException.__init__(self, message)
        self.type = type

    def __str__(self):
        if self.message:
            return self.message
        elif self.type == self.UNKNOWN_METHOD:
            return 'Unknown method'
        elif self.type == self.INVALID_MESSAGE_TYPE:
            return 'Invalid message type'
        elif self.type == self.WRONG_METHOD_NAME:
            return 'Wrong method name'
        elif self.type == self.BAD_SEQUENCE_ID:
            return 'Bad sequence ID'
        elif self.type == self.MISSING_RESULT:
            return 'Missing result'
        elif self.type == self.INTERNAL_ERROR:
            return 'Internal error'
        elif self.type == self.PROTOCOL_ERROR:
            return 'Protocol error'
        elif self.type == self.INVALID_TRANSFORM:
            return 'Invalid transform'
        elif self.type == self.INVALID_PROTOCOL:
            return 'Invalid protocol'
        elif self.type == self.UNSUPPORTED_CLIENT_TYPE:
            return 'Unsupported client type'
        else:
            return 'Default (unknown) TApplicationException'

    def read(self, iprot):
        iprot.readStructBegin()
        while True:
            (fname, ftype, fid) = iprot.readFieldBegin()
            if ftype == TType.STOP:
                break
            if fid == 1:
                if ftype == TType.STRING:
                    self.message = iprot.readString()
                else:
                    iprot.skip(ftype)
            elif fid == 2:
                if ftype == TType.I32:
                    self.type = iprot.readI32()
                else:
                    iprot.skip(ftype)
            else:
                iprot.skip(ftype)
            iprot.readFieldEnd()
        iprot.readStructEnd()

    def write(self, oprot):
        oprot.writeStructBegin('TApplicationException')
        if self.message is not None:
            oprot.writeFieldBegin('message', TType.STRING, 1)
            oprot.writeString(self.message)
            oprot.writeFieldEnd()
        if self.type is not None:
            oprot.writeFieldBegin('type', TType.I32, 2)
            oprot.writeI32(self.type)
            oprot.writeFieldEnd()
        oprot.writeFieldStop()
        oprot.writeStructEnd()


class TFrozenDict(dict):

    def __init__(self, *args, **kwargs):
        super(TFrozenDict, self).__init__(*args, **kwargs)
        self.__hashval = hash(TFrozenDict) ^ hash(tuple(sorted(self.items())))

    def __setitem__(self, *args):
        raise TypeError("Can't modify frozen TFreezableDict")

    def __delitem__(self, *args):
        raise TypeError("Can't modify frozen TFreezableDict")

    def __hash__(self):
        return self.__hashval

class TProtocolException(TException):

    UNKNOWN = 0
    INVALID_DATA = 1
    NEGATIVE_SIZE = 2
    SIZE_LIMIT = 3
    BAD_VERSION = 4
    NOT_IMPLEMENTED = 5
    DEPTH_LIMIT = 6

    def __init__(self, type=UNKNOWN, message=None):
        TException.__init__(self, message)
        self.type = type

def checkIntegerLimits(i, bits):
    if bits == 8 and (i < -128 or i > 127):
        raise TProtocolException(TProtocolException.INVALID_DATA, "i8 requires -128 <= number <= 127")
    elif bits == 16 and (i < -32768 or i > 32767):
        raise TProtocolException(TProtocolException.INVALID_DATA, "i16 requires -32768 <= number <= 32767")
    elif bits == 32 and (i < -2147483648 or i > 2147483647):
        raise TProtocolException(TProtocolException.INVALID_DATA, "i32 requires -2147483648 <= number <= 2147483647")
    elif bits == 64 and (i < -9223372036854775808 or i > 9223372036854775807):
        raise TProtocolException(TProtocolException.INVALID_DATA, "i64 requires -9223372036854775808 <= number <= 9223372036854775807")


class TProtocolBase(object):

    def __init__(self, trans):
        self.trans = trans
        self._fast_decode = None
        self._fast_encode = None

    @staticmethod
    def _check_length(limit, length):
        if length < 0:
            raise TTransportException(TTransportException.NEGATIVE_SIZE, 'Negative length: %d' % length)
        if limit is not None and length > limit:
            raise TTransportException(TTransportException.SIZE_LIMIT, 'Length exceeded max allowed: %d' % limit)

    def writeMessageBegin(self, name, ttype, seqid):
        pass

    def writeMessageEnd(self):
        pass

    def writeStructBegin(self, name):
        pass

    def writeStructEnd(self):
        pass

    def writeFieldBegin(self, name, ttype, fid):
        pass

    def writeFieldEnd(self):
        pass

    def writeFieldStop(self):
        pass

    def writeMapBegin(self, ktype, vtype, size):
        pass

    def writeMapEnd(self):
        pass

    def writeListBegin(self, etype, size):
        pass

    def writeListEnd(self):
        pass

    def writeSetBegin(self, etype, size):
        pass

    def writeSetEnd(self):
        pass

    def writeBool(self, bool_val):
        pass

    def writeByte(self, byte):
        pass

    def writeI16(self, i16):
        pass

    def writeI32(self, i32):
        pass

    def writeI64(self, i64):
        pass

    def writeDouble(self, dub):
        pass

    def writeString(self, str_val):
        self.writeBinary(str_to_binary(str_val))

    def writeBinary(self, str_val):
        pass

    def writeUtf8(self, str_val):
        self.writeString(str_val.encode('utf8'))

    def readMessageBegin(self):
        pass

    def readMessageEnd(self):
        pass

    def readStructBegin(self):
        pass

    def readStructEnd(self):
        pass

    def readFieldBegin(self):
        pass

    def readFieldEnd(self):
        pass

    def readMapBegin(self):
        pass

    def readMapEnd(self):
        pass

    def readListBegin(self):
        pass

    def readListEnd(self):
        pass

    def readSetBegin(self):
        pass

    def readSetEnd(self):
        pass

    def readBool(self):
        pass

    def readByte(self):
        pass

    def readI16(self):
        pass

    def readI32(self):
        pass

    def readI64(self):
        pass

    def readDouble(self):
        pass

    def readString(self):
        return binary_to_str(self.readBinary())

    def readBinary(self):
        pass

    def readUtf8(self):
        return self.readString().decode('utf8')

    def skip(self, ttype):
        if ttype == TType.STOP:
            return
        elif ttype == TType.BOOL:
            self.readBool()
        elif ttype == TType.BYTE:
            self.readByte()
        elif ttype == TType.I16:
            self.readI16()
        elif ttype == TType.I32:
            self.readI32()
        elif ttype == TType.I64:
            self.readI64()
        elif ttype == TType.DOUBLE:
            self.readDouble()
        elif ttype == TType.STRING:
            self.readString()
        elif ttype == TType.STRUCT:
            name = self.readStructBegin()
            while True:
                (name, ttype, id) = self.readFieldBegin()
                if ttype == TType.STOP:
                    break
                self.skip(ttype)
                self.readFieldEnd()
            self.readStructEnd()
        elif ttype == TType.MAP:
            (ktype, vtype, size) = self.readMapBegin()
            for i in range(size):
                self.skip(ktype)
                self.skip(vtype)
            self.readMapEnd()
        elif ttype == TType.SET:
            (etype, size) = self.readSetBegin()
            for i in range(size):
                self.skip(etype)
            self.readSetEnd()
        elif ttype == TType.LIST:
            (etype, size) = self.readListBegin()
            for i in range(size):
                self.skip(etype)
            self.readListEnd()

    # tuple of: ( 'reader method' name, is_container bool, 'writer_method' name )
    _TTYPE_HANDLERS = (
        (None, None, False),  # 0 TType.STOP
        (None, None, False),  # 1 TType.VOID # TODO: handle void?
        ('readBool', 'writeBool', False),  # 2 TType.BOOL
        ('readByte', 'writeByte', False),  # 3 TType.BYTE and I08
        ('readDouble', 'writeDouble', False),  # 4 TType.DOUBLE
        (None, None, False),  # 5 undefined
        ('readI16', 'writeI16', False),  # 6 TType.I16
        (None, None, False),  # 7 undefined
        ('readI32', 'writeI32', False),  # 8 TType.I32
        (None, None, False),  # 9 undefined
        ('readI64', 'writeI64', False),  # 10 TType.I64
        ('readString', 'writeString', False),  # 11 TType.STRING and UTF7
        ('readContainerStruct', 'writeContainerStruct', True),  # 12 *.STRUCT
        ('readContainerMap', 'writeContainerMap', True),  # 13 TType.MAP
        ('readContainerSet', 'writeContainerSet', True),  # 14 TType.SET
        ('readContainerList', 'writeContainerList', True),  # 15 TType.LIST
        (None, None, False),  # 16 TType.UTF8 # TODO: handle utf8 types?
        (None, None, False)  # 17 TType.UTF16 # TODO: handle utf16 types?
    )

    def _ttype_handlers(self, ttype, spec):
        if spec == 'BINARY':
            if ttype != TType.STRING:
                raise TProtocolException(type=TProtocolException.INVALID_DATA, message='Invalid binary field type %d' % ttype)
            return ('readBinary', 'writeBinary', False)
        if sys.version_info[0] == 2 and spec == 'UTF8':
            if ttype != TType.STRING:
                raise TProtocolException(type=TProtocolException.INVALID_DATA, message='Invalid string field type %d' % ttype)
            return ('readUtf8', 'writeUtf8', False)
        return self._TTYPE_HANDLERS[ttype] if ttype < len(self._TTYPE_HANDLERS) else (None, None, False)

    def _read_by_ttype(self, ttype, spec, espec):
        reader_name, _, is_container = self._ttype_handlers(ttype, spec)
        if reader_name is None:
            raise TProtocolException(type=TProtocolException.INVALID_DATA, message='Invalid type %d' % (ttype))
        reader_func = getattr(self, reader_name)
        read = (lambda: reader_func(espec)) if is_container else reader_func
        while True:
            yield read()

    def readFieldByTType(self, ttype, spec):
        return next(self._read_by_ttype(ttype, spec, spec))

    def readContainerList(self, spec):
        ttype, tspec, is_immutable = spec
        (list_type, list_len) = self.readListBegin()
        elems = islice(self._read_by_ttype(ttype, spec, tspec), list_len)
        results = (tuple if is_immutable else list)(elems)
        self.readListEnd()
        return results

    def readContainerSet(self, spec):
        ttype, tspec, is_immutable = spec
        (set_type, set_len) = self.readSetBegin()
        # TODO: compare types we just decoded with thrift_spec
        elems = islice(self._read_by_ttype(ttype, spec, tspec), set_len)
        results = (frozenset if is_immutable else set)(elems)
        self.readSetEnd()
        return results

    def readContainerStruct(self, spec):
        (obj_class, obj_spec) = spec
        obj = obj_class()
        obj.read(self)
        return obj

    def readContainerMap(self, spec):
        ktype, kspec, vtype, vspec, is_immutable = spec
        (map_ktype, map_vtype, map_len) = self.readMapBegin()
        keys = self._read_by_ttype(ktype, spec, kspec)
        vals = self._read_by_ttype(vtype, spec, vspec)
        keyvals = islice(zip(keys, vals), map_len)
        results = (TFrozenDict if is_immutable else dict)(keyvals)
        self.readMapEnd()
        return results

    def readStruct(self, obj, thrift_spec, is_immutable=False):
        if is_immutable:
            fields = {}
        self.readStructBegin()
        while True:
            (fname, ftype, fid) = self.readFieldBegin()
            if ftype == TType.STOP:
                break
            try:
                field = thrift_spec[fid]
            except IndexError:
                self.skip(ftype)
            else:
                if field is not None and ftype == field[1]:
                    fname = field[2]
                    fspec = field[3]
                    val = self.readFieldByTType(ftype, fspec)
                    if is_immutable:
                        fields[fname] = val
                    else:
                        setattr(obj, fname, val)
                else:
                    self.skip(ftype)
            self.readFieldEnd()
        self.readStructEnd()
        if is_immutable:
            return obj(**fields)

    def writeContainerStruct(self, val, spec):
        val.write(self)

    def writeContainerList(self, val, spec):
        ttype, tspec, _ = spec
        self.writeListBegin(ttype, len(val))
        for _ in self._write_by_ttype(ttype, val, spec, tspec):
            pass
        self.writeListEnd()

    def writeContainerSet(self, val, spec):
        ttype, tspec, _ = spec
        self.writeSetBegin(ttype, len(val))
        for _ in self._write_by_ttype(ttype, val, spec, tspec):
            pass
        self.writeSetEnd()

    def writeContainerMap(self, val, spec):
        ktype, kspec, vtype, vspec, _ = spec
        self.writeMapBegin(ktype, vtype, len(val))
        for _ in zip(self._write_by_ttype(ktype, Six.iterkeys(val), spec, kspec),
                     self._write_by_ttype(vtype, Six.itervalues(val), spec, vspec)):
            pass
        self.writeMapEnd()

    def writeStruct(self, obj, thrift_spec):
        self.writeStructBegin(obj.__class__.__name__)
        for field in thrift_spec:
            if field is None:
                continue
            fname = field[2]
            val = getattr(obj, fname)
            if val is None:
                # skip writing out unset fields
                continue
            fid = field[0]
            ftype = field[1]
            fspec = field[3]
            self.writeFieldBegin(fname, ftype, fid)
            self.writeFieldByTType(ftype, val, fspec)
            self.writeFieldEnd()
        self.writeFieldStop()
        self.writeStructEnd()

    def _write_by_ttype(self, ttype, vals, spec, espec):
        _, writer_name, is_container = self._ttype_handlers(ttype, spec)
        writer_func = getattr(self, writer_name)
        write = (lambda v: writer_func(v, espec)) if is_container else writer_func
        for v in vals:
            yield write(v)

    def writeFieldByTType(self, ttype, val, spec):
        next(self._write_by_ttype(ttype, [val], spec, spec))

class TTransportException(TException):

    UNKNOWN = 0
    NOT_OPEN = 1
    ALREADY_OPEN = 2
    TIMED_OUT = 3
    END_OF_FILE = 4
    NEGATIVE_SIZE = 5
    SIZE_LIMIT = 6

    def __init__(self, type=UNKNOWN, message=None):
        TException.__init__(self, message)
        self.type = type


class TTransportBase(object):

    def isOpen(self):
        pass

    def open(self):
        pass

    def close(self):
        pass

    def read(self, sz):
        pass

    def readAll(self, sz):
        buff = b''
        have = 0
        while (have < sz):
            chunk = self.read(sz - have)
            have += len(chunk)
            buff += chunk

            if len(chunk) == 0:
                raise EOFError()

        return buff

    def write(self, buf):
        pass

    def flush(self):
        pass

class TCompactProtocol(TProtocolBase):

    PROTOCOL_ID = 0x82
    VERSION = 1
    VERSION_MASK = 0x1f
    TYPE_MASK = 0xe0
    TYPE_BITS = 0x07
    TYPE_SHIFT_AMOUNT = 5

    def __init__(self, trans,
                 string_length_limit=None,
                 container_length_limit=None):
        TProtocolBase.__init__(self, trans)
        self.state = 0
        self.__last_fid = 0
        self.__bool_fid = None
        self.__bool_value = None
        self.__structs = []
        self.__containers = []
        self.string_length_limit = string_length_limit
        self.container_length_limit = container_length_limit

    def _check_string_length(self, length):
        self._check_length(self.string_length_limit, length)

    def _check_container_length(self, length):
        self._check_length(self.container_length_limit, length)

    def __writeVarint(self, n):
        writeVarint(self.trans, n)

    def writeMessageBegin(self, name, type, seqid):
        assert self.state == 0
        self.__writeUByte(self.PROTOCOL_ID)
        self.__writeUByte(self.VERSION | (type << self.TYPE_SHIFT_AMOUNT))
        self.__writeVarint(seqid)
        self.__writeBinary(str_to_binary(name))
        self.state = 2

    def writeMessageEnd(self):
        assert self.state == 2
        self.state = 0

    def writeStructBegin(self, name):
        assert self.state in (0, 3, 2), self.state
        self.__structs.append((self.state, self.__last_fid))
        self.state = 1
        self.__last_fid = 0

    def writeStructEnd(self):
        assert self.state == 1
        self.state, self.__last_fid = self.__structs.pop()

    def writeFieldStop(self):
        self.__writeByte(0)

    def __writeFieldHeader(self, type, fid):
        delta = fid - self.__last_fid
        if 0 < delta <= 15:
            self.__writeUByte(delta << 4 | type)
        else:
            self.__writeByte(type)
            self.__writeI16(fid)
        self.__last_fid = fid

    def writeFieldBegin(self, name, type, fid):
        assert self.state == 1, self.state
        if type == TType.BOOL:
            self.state = 4
            self.__bool_fid = fid
        else:
            self.state = 2
            self.__writeFieldHeader(CTYPES[type], fid)

    def writeFieldEnd(self):
        assert self.state in (2, 4), self.state
        self.state = 1

    def __writeUByte(self, byte):
        self.trans.write(pack('!B', byte))

    def __writeByte(self, byte):
        self.trans.write(pack('!b', byte))

    def __writeI16(self, i16):
        self.__writeVarint(makeZigZag(i16, 16))

    def __writeSize(self, i32):
        self.__writeVarint(i32)

    def writeCollectionBegin(self, etype, size):
        assert self.state in (2, 3), self.state
        if size <= 14:
            self.__writeUByte(size << 4 | CTYPES[etype])
        else:
            self.__writeUByte(0xf0 | CTYPES[etype])
            self.__writeSize(size)
        self.__containers.append(self.state)
        self.state = 3
    writeSetBegin = writeCollectionBegin
    writeListBegin = writeCollectionBegin

    def writeMapBegin(self, ktype, vtype, size):
        assert self.state in (2, 3), self.state
        if size == 0:
            self.__writeByte(0)
        else:
            self.__writeSize(size)
            self.__writeUByte(CTYPES[ktype] << 4 | CTYPES[vtype])
        self.__containers.append(self.state)
        self.state = 3

    def writeCollectionEnd(self):
        assert self.state == 3, self.state
        self.state = self.__containers.pop()
    writeMapEnd = writeCollectionEnd
    writeSetEnd = writeCollectionEnd
    writeListEnd = writeCollectionEnd

    def writeBool(self, bool):
        if self.state == 4:
            if bool:
                ctype = CompactType.TRUE
            else:
                ctype = CompactType.FALSE
            self.__writeFieldHeader(ctype, self.__bool_fid)
        elif self.state == 3:
            if bool:
                self.__writeByte(CompactType.TRUE)
            else:
                self.__writeByte(CompactType.FALSE)
        else:
            raise AssertionError("Invalid state in compact protocol")

    writeByte = writer(__writeByte)
    writeI16 = writer(__writeI16)

    @writer
    def writeI32(self, i32):
        self.__writeVarint(makeZigZag(i32, 32))

    @writer
    def writeI64(self, i64):
        self.__writeVarint(makeZigZag(i64, 64))

    @writer
    def writeDouble(self, dub):
        self.trans.write(pack('<d', dub))

    def __writeBinary(self, s):
        self.__writeSize(len(s))
        self.trans.write(s)
    writeBinary = writer(__writeBinary)

    def readFieldBegin(self):
        assert self.state == 5, self.state
        type = self.__readUByte()
        if type & 0x0f == TType.STOP:
            return (None, 0, 0)
        delta = type >> 4
        if delta == 0:
            fid = self.__readI16()
        else:
            fid = self.__last_fid + delta
        self.__last_fid = fid
        type = type & 0x0f
        if type == CompactType.TRUE:
            self.state = 8
            self.__bool_value = True
        elif type == CompactType.FALSE:
            self.state = 8
            self.__bool_value = False
        else:
            self.state = 7
        return (None, self.__getTType(type), fid)

    def readFieldEnd(self):
        assert self.state in (7, 8), self.state
        self.state = 5

    def __readUByte(self):
        result, = unpack('!B', self.trans.readAll(1))
        return result

    def __readByte(self):
        result, = unpack('!b', self.trans.readAll(1))
        return result

    def __readVarint(self):
        return readVarint(self.trans)

    def __readZigZag(self):
        return fromZigZag(self.__readVarint())

    def __readSize(self):
        result = self.__readVarint()
        if result < 0:
            raise TProtocolException("Length < 0")
        return result

    def readMessageBegin(self):
        assert self.state == 0
        proto_id = self.__readUByte()
        if proto_id != self.PROTOCOL_ID:
            raise TProtocolException(TProtocolException.BAD_VERSION, 'Bad protocol id in the message: %d' % proto_id)
        ver_type = self.__readUByte()
        type = (ver_type >> self.TYPE_SHIFT_AMOUNT) & self.TYPE_BITS
        version = ver_type & self.VERSION_MASK
        if version != self.VERSION:
            raise TProtocolException(TProtocolException.BAD_VERSION, 'Bad version: %d (expect %d)' % (version, self.VERSION))
        seqid = self.__readVarint()
        name = binary_to_str(self.__readBinary())
        return (name, type, seqid)

    def readMessageEnd(self):
        assert self.state == 0
        assert len(self.__structs) == 0

    def readStructBegin(self):
        assert self.state in (0, 6, 7), self.state
        self.__structs.append((self.state, self.__last_fid))
        self.state = 5
        self.__last_fid = 0

    def readStructEnd(self):
        assert self.state == 5
        self.state, self.__last_fid = self.__structs.pop()

    def readCollectionBegin(self):
        assert self.state in (7, 6), self.state
        size_type = self.__readUByte()
        size = size_type >> 4
        type = self.__getTType(size_type)
        if size == 15:
            size = self.__readSize()
        self._check_container_length(size)
        self.__containers.append(self.state)
        self.state = 6
        return type, size
    readSetBegin = readCollectionBegin
    readListBegin = readCollectionBegin

    def readMapBegin(self):
        assert self.state in (7, 6), self.state
        size = self.__readSize()
        self._check_container_length(size)
        types = 0
        if size > 0:
            types = self.__readUByte()
        vtype = self.__getTType(types)
        ktype = self.__getTType(types >> 4)
        self.__containers.append(self.state)
        self.state = 6
        return (ktype, vtype, size)

    def readCollectionEnd(self):
        assert self.state == 6, self.state
        self.state = self.__containers.pop()
    readSetEnd = readCollectionEnd
    readListEnd = readCollectionEnd
    readMapEnd = readCollectionEnd

    def readBool(self):
        if self.state == 8:
            return self.__bool_value == CompactType.TRUE
        elif self.state == 6:
            return self.__readByte() == CompactType.TRUE
        else:
            raise AssertionError("Invalid state in compact protocol: %d" % self.state)

    readByte = reader(__readByte)
    __readI16 = __readZigZag
    readI16 = reader(__readZigZag)
    readI32 = reader(__readZigZag)
    readI64 = reader(__readZigZag)

    @reader
    def readDouble(self):
        buff = self.trans.readAll(8)
        val, = unpack('<d', buff)
        return val

    def __readBinary(self):
        size = self.__readSize()
        self._check_string_length(size)
        return self.trans.readAll(size)
    readBinary = reader(__readBinary)

    def __getTType(self, byte):
        return TTYPES[byte & 0x0f]

class TCompactProtocolAccelerated(TCompactProtocol):
    """C-Accelerated version of TCompactProtocol.

    This class does not override any of TCompactProtocol's methods,
    but the generated code recognizes it directly and will call into
    our C module to do the encoding, bypassing this object entirely.
    We inherit from TCompactProtocol so that the normal TCompactProtocol
    encoding can happen if the fastbinary module doesn't work for some
    reason.
    To disable this behavior, pass fallback=False constructor argument.

    In order to take advantage of the C module, just use
    TCompactProtocolAccelerated instead of TCompactProtocol.
    """

    def __init__(self, *args, **kwargs):
        fallback = kwargs.pop('fallback', True)
        super(TCompactProtocolAccelerated, self).__init__(*args, **kwargs)
        try:
            from thrift.protocol import fastbinary
        except ImportError:
            if not fallback:
                raise
        else:
            self._fast_decode = fastbinary.decode_compact
            self._fast_encode = fastbinary.encode_compact

class THttpClient(TTransportBase):

    def __init__(self, uri_or_host, port=None, path=None):

        if port is not None:
            warnings.warn("Please use the THttpClient('http://host:port/path') syntax", DeprecationWarning, stacklevel=2)
            self.host = uri_or_host
            self.port = port
            assert path
            self.path = path
            self.scheme = 'http'
        else:
            parsed = urllib.parse.urlparse(uri_or_host)
            self.scheme = parsed.scheme
            assert self.scheme in ('http', 'https')
            if self.scheme == 'http':
                self.port = parsed.port or http_client.HTTP_PORT
            elif self.scheme == 'https':
                self.port = parsed.port or http_client.HTTPS_PORT
            self.host = parsed.hostname
            self.path = parsed.path
            if parsed.query:
                self.path += '?%s' % parsed.query
        proxy = None
        self.realhost = self.realport = self.proxy_auth = None
        self.__wbuf = BytesIO()
        self.__http = None
        self.__http_response = None
        self.__timeout = None
        self.__custom_headers = None
        self.__time = time.time()
        self.__loop = 0

    @staticmethod
    def basic_proxy_auth_header(proxy):
        if proxy is None or not proxy.username:
            return None
        ap = "%s:%s" % (urllib.parse.unquote(proxy.username),
                        urllib.parse.unquote(proxy.password))
        cr = base64.b64encode(ap).strip()
        return "Basic " + cr

    def using_proxy(self):
        return self.realhost is not None

    def open(self):
        if self.scheme == 'http':
            self.__http = http_client.HTTPConnection(self.host, self.port)
        elif self.scheme == 'https':
            self.__http = http_client.HTTPSConnection(self.host, self.port)

    def close(self):
        self.__http.close()
        self.__http = None
        self.__http_response = None

    def isOpen(self):
        return self.__http is not None

    def setTimeout(self, ms):
        if not hasattr(socket, 'getdefaulttimeout'):
            raise NotImplementedError

        if ms is None:
            self.__timeout = None
        else:
            self.__timeout = ms / 1000.0

    def setCustomHeaders(self, headers):
        self.__custom_headers = headers

    def read(self, sz):
        return self.__http_response.read(sz)

    def write(self, buf):
        self.__wbuf.write(buf)

    def __withTimeout(f):
        def _f(*args, **kwargs):
            orig_timeout = socket.getdefaulttimeout()
            socket.setdefaulttimeout(args[0].__timeout)
            try:
                result = f(*args, **kwargs)
            finally:
                socket.setdefaulttimeout(orig_timeout)
            return result
        return _f

    def flush(self):
        if self.__loop <= 2:
            if self.isOpen(): self.close()
            self.open(); self.__loop += 1
        elif time.time() - self.__time > 90:
            self.close(); self.open(); self.__time = time.time()

        # Pull data out of buffer
        data = self.__wbuf.getvalue()
        self.__wbuf = BytesIO()

        self.__http.putrequest('POST', self.path)

        # Write headers
        self.__http.putheader('Host', self.host)
        self.__http.putheader('Content-Type', 'application/x-thrift')
        self.__http.putheader('Content-Length', str(len(data)))
        if self.__custom_headers:
            for key, val in Six.iteritems(self.__custom_headers):
                self.__http.putheader(key, val)

        self.__http.endheaders()

        # Write payload
        self.__http.send(data)

        # Get reply to flush the request
        self.__http_response = self.__http.getresponse()
        self.code = self.__http_response.status
        self.message = self.__http_response.reason
        self.headers = self.__http_response.msg
