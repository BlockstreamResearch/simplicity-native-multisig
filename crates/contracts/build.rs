fn main() {
    println!("cargo:rerun-if-changed=Simplex.toml");
    println!("cargo:rerun-if-changed=simf");

    let src_dir = String::from("simf");
    let simf_files = vec![String::from("*.simf")];

    let simfs = smplx_build::ArtifactsResolver::resolve_files_to_build(&src_dir, &simf_files)
        .expect("failed to resolve Simplex contract sources");
    let out_dir = smplx_build::ArtifactsResolver::resolve_local_dir(&"src/artifacts")
        .expect("failed to resolve generated artifact directory");
    let base_dir = std::env::current_dir()
        .expect("failed to read current directory")
        .join(&src_dir)
        .canonicalize()
        .expect("failed to canonicalize Simplex source directory");

    smplx_build::ArtifactsGenerator::generate_artifacts(out_dir, base_dir, &simfs)
        .expect("failed to generate Simplex artifacts");
}
