#!/usr/bin/env python3
"""Passive ELF64 dependency inventory; never run or load a guest object on the host."""
# §AR-workspace.runtime: Presence/hash evidence complements actual VM loader tests, not linker
# verification.
import hashlib
import posixpath
import struct


def elf(data):
    if len(data)<64 or data[:7]!=b'\x7fELF\x02\x01\x01':raise ValueError('Unsupported ELF ABI')
    _,kind,machine,version,_,offset,_,_,header,entry,count,_,_,_=struct.unpack_from('<16sHHIQQQIHHHHHH',data)
    if kind not in (2,3) or machine!=62 or version!=1 or header!=64 or entry!=56 or count==65535 or offset+entry*count>len(data):
        raise ValueError('Malformed ELF header/program table')
    segments=[]
    for i in range(count):
        typ,flags,off,addr,physical,filesz,memsz,alignment=struct.unpack_from('<IIQQQQQQ',data,offset+i*entry)
        if off+filesz>len(data) or addr+memsz>2**64 or filesz>memsz:raise ValueError('ELF segment overflow')
        segments.append((typ,off,addr,filesz,memsz))
    def string(raw):
        end=raw.find(b'\0')
        if end<0:raise ValueError('Unterminated ELF string')
        return raw[:end].decode('utf-8')
    interpreters=[string(data[o:o+n]) for t,o,a,n,m in segments if t==3]
    if len(interpreters)>1:raise ValueError('Multiple ELF interpreters')
    dynamic=[(o,n) for t,o,a,n,m in segments if t==2]
    if len(dynamic)>1:raise ValueError('Multiple ELF dynamic tables')
    if not dynamic:return {'interpreter':interpreters[0] if interpreters else None,'needed':[],'rpath':[],'runpath':[]}
    off,size=dynamic[0]
    if size%16:raise ValueError('Partial ELF dynamic entry')
    tags=[]
    for i in range(size//16):
        tag,value=struct.unpack_from('<qQ',data,off+i*16)
        if tag==0:break
        tags.append((tag,value))
    else:raise ValueError('Unterminated ELF dynamic table')
    pointers=[v for t,v in tags if t==5];sizes=[v for t,v in tags if t==10]
    if len(pointers)!=1 or len(sizes)!=1:raise ValueError('Ambiguous ELF string table')
    pointer=pointers[0];size=sizes[0]
    mappings=[o+pointer-a for t,o,a,n,m in segments if t==1 and a<=pointer and pointer+size<=a+n]
    if len(mappings)!=1:raise ValueError('Unmapped ELF string table')
    strings=data[mappings[0]:mappings[0]+size]
    def names(tag):
        result=[]
        for t,v in tags:
            if t==tag:
                if v>=len(strings):raise ValueError('ELF string offset out of bounds')
                result.append(string(strings[v:]))
        return result
    return {'interpreter':interpreters[0] if interpreters else None,'needed':names(1),'rpath':names(15),'runpath':names(29)}


def inventory(entries,resolve):
    records={}
    for name,entry in sorted(entries.items()):
        if entry['kind']!='file' or not entry['data'].startswith(b'\x7fELF'):continue
        if struct.unpack_from('<H',entry['data'],16)[0]==1:
            records['/'+name]={'elf_kind':'relocatable-link-input','sha256':hashlib.sha256(entry['data']).hexdigest()};continue
        record=elf(entry['data']);dependencies={}
        search=[]
        for paths in record['runpath'] or record['rpath']:
            for path in paths.split(':'):
                path=path.replace('${ORIGIN}', '/'+posixpath.dirname(name)).replace('$ORIGIN','/'+posixpath.dirname(name))
                if not path.startswith('/') or '$' in path:raise ValueError('Unsupported ELF search path')
                search.append(posixpath.normpath(path))
        search += ['/usr/local/lib','/lib/x86_64-linux-gnu','/usr/lib/x86_64-linux-gnu','/lib','/usr/lib']
        for dependency in record['needed']:
            candidates=[dependency] if '/' in dependency else [posixpath.join(directory,dependency) for directory in search]
            resolved=None
            for path in candidates:
                try:target=resolve(entries,path)
                except ValueError:continue
                if target in entries and entries[target]['kind']=='file':resolved=target;break
            if resolved is None:
                if name == 'usr/local/lib/python3.13/lib-dynload/_tkinter.cpython-313-x86_64-linux-gnu.so':
                    dependencies[dependency]={'unsupported_optional':True};continue
                raise ValueError(f'Missing dependency {dependency} of {name}')
            dependencies[dependency]={'path':'/'+resolved,'sha256':hashlib.sha256(entries[resolved]['data']).hexdigest()}
        if record['interpreter']:
            path=resolve(entries,record['interpreter'])
            if path not in entries or entries[path]['kind']!='file':raise ValueError('Missing interpreter')
            record['interpreter_resolved']='/'+path
        record['dependencies']=dependencies;record['sha256']=hashlib.sha256(entry['data']).hexdigest();records['/'+name]=record
    return records
