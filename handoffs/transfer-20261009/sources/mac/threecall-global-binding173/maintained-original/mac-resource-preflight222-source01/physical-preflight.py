def physical_preflight(config):
    # Early admission only; full artifact census remains immediately pre-Popen
    # under owned lock and after compilation and final receipt publication.
    stat=os.statvfs(config['batch_root']); disk=stat.f_bavail*stat.f_frsize
    memory=free_memory()
    require(disk>=2*1024*1024*1024 and memory>=15, 'RAM/disk admission')
    return {'free_memory_percent':memory,'free_disk_bytes':disk}

