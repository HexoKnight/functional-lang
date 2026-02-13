fn parse(src, file: FileId) -> IR

fn validate(AST, file_resolver: rel_file_name -> FileId, file: FileId) -> (IR, dependencies: {FileId: FileId})
  Err: display(file_name, )

fn validate_rec(FileId, file_resolver: rel_file_name -> FileId, parser: FileId -> AST, file: FileId) -> {FileId: IR}

fn type_check(FileId, {FileId: IR}) -> TIR
