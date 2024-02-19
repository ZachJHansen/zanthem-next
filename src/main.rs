pub mod command_line;
pub mod convenience;
pub mod formatting;
pub mod parsing;
pub mod proof_search;
pub mod simplifying;
pub mod syntax_tree;
pub mod translating;

use pretty::{BoxAllocator, DocAllocator, DocBuilder};

use {
    crate::{
        command_line::{Arguments, Command, Translation, Verification},
        proof_search::{problem, vampire},
        simplifying::fol::ht as ht_simplifications,
        syntax_tree::{asp, fol},
        translating::completion::completion,
        translating::gamma::gamma,
        translating::tau_star::tau_star,
    },
    anyhow::{Context, Result},
    clap::Parser as _,
    lazy_static::lazy_static,
    regex::Regex,
    std::{
        fs::{read_dir, read_to_string},
        io,
        path::PathBuf,
    },
};

lazy_static! {
    static ref HELP: Regex = Regex::new(r"\.help\.spec$").unwrap();
}

fn verify(
    with: Verification,
    program: PathBuf,
    specification: PathBuf,
    user_guide: PathBuf,
    lemmas: Option<PathBuf>,
    cores: u16,
    break_equivalences: bool,
    parallelize: bool,
    simplify: bool,
) -> Result<()> {
    let spec = match specification.extension() {
        Some(extension) => match extension.to_str() {
            Some(ext) => match ext {
                "lp" => {
                    let prog2: asp::Program = read_to_string(&specification)
                        .with_context(|| format!("failed to read '{}'", &specification.display()))?
                        .parse()
                        .with_context(|| {
                            format!("failed to parse '{}'", &specification.display())
                        })?;
                    problem::FileType::MiniGringoProgram { program: prog2 }
                }
                "spec" => {
                    let specification: fol::Specification = read_to_string(&specification)
                        .with_context(|| format!("failed to read '{}'", &specification.display()))?
                        .parse()
                        .with_context(|| {
                            format!("failed to parse '{}'", &specification.display())
                        })?;

                    problem::FileType::FirstOrderSpecification { specification }
                }
                _ => {
                    todo!()
                }
            },
            None => todo!(),
        },
        None => {
            todo!()
        }
    };

    let prog: asp::Program = read_to_string(&program)
        .with_context(|| format!("failed to read '{}'", &program.display()))?
        .parse()
        .with_context(|| format!("failed to parse '{}'", &program.display()))?;

    let ug: fol::Specification = read_to_string(&user_guide)
        .with_context(|| format!("failed to read '{}'", &user_guide.display()))?
        .parse()
        .with_context(|| format!("failed to parse '{}'", &user_guide.display()))?;

    let lem = match lemmas {
        Some(l) => {
            let lem: fol::Specification = read_to_string(&l)
                .with_context(|| format!("failed to read '{}'", &l.display()))?
                .parse()
                .with_context(|| format!("failed to parse '{}'", &l.display()))?;
            Some(lem)
        }
        None => None,
    };

    match with {
        Verification::Default => {
            vampire::default_verification(
                &prog,
                &spec,
                &ug,
                lem,
                cores,
                break_equivalences,
                parallelize,
                simplify,
            );
        }
        Verification::Sequential => {
            vampire::sequential_verification(
                &prog,
                &spec,
                &ug,
                lem,
                cores,
                break_equivalences,
                parallelize,
                simplify,
            );
        }
    }
    Ok(())
}

fn collect_files(dir: PathBuf) -> io::Result<Vec<PathBuf>> {
    let mut files = vec![];
    if dir.is_dir() {
        for entry in read_dir(dir)? {
            let entry = entry?;
            let meta = entry.metadata()?;
            if meta.is_file() {
                files.push(entry.path());
            }
        }
    }
    core::result::Result::Ok(files)
}




#[derive(Clone, Debug)]
pub struct Forest<'a>(&'a [Tree<'a>]);

impl<'a> Forest<'a> {
    fn forest(forest: &'a [Tree<'a>]) -> Forest<'a> {
        Forest(forest)
    }

    fn nil() -> Forest<'a> {
        Forest(&[])
    }

    fn bracket<'b, D, A>(&'b self, allocator: &'b D) -> DocBuilder<'b, D, A>
    where
        D: DocAllocator<'b, A>,
        D::Doc: Clone,
        A: Clone,
    {
        if (self.0).is_empty() {
            allocator.nil()
        } else {
            allocator
                .text("[")
                .append(allocator.hardline().append(self.pretty(allocator)).nest(2))
                .append(allocator.hardline())
                .append(allocator.text("]"))
        }
    }

    fn pretty<'b, D, A>(&'b self, allocator: &'b D) -> DocBuilder<'b, D, A>
    where
        D: DocAllocator<'b, A>,
        D::Doc: Clone,
        A: Clone,
    {
        let forest = self.0;
        let separator = allocator.text(",").append(allocator.hardline());
        allocator.intersperse(forest.iter().map(|tree| tree.pretty(allocator)), separator)
    }
}

#[derive(Clone, Debug)]
pub struct Tree<'a> {
    node: String,
    forest: Forest<'a>,
}

impl<'a> Tree<'a> {
    pub fn node(node: &str) -> Tree<'a> {
        Tree {
            node: node.to_string(),
            forest: Forest::nil(),
        }
    }

    pub fn node_with_forest(node: &str, forest: &'a [Tree<'a>]) -> Tree<'a> {
        Tree {
            node: node.to_string(),
            forest: Forest::forest(forest),
        }
    }

    pub fn pretty<'b, D, A>(&'b self, allocator: &'b D) -> DocBuilder<'b, D, A>
    where
        D: DocAllocator<'b, A>,
        D::Doc: Clone,
        A: Clone,
    {
        allocator
            .text(&self.node[..])
            .append((self.forest).bracket(allocator))
            .group()
    }
}

fn main() -> Result<()> {
    env_logger::init();


    let allocator = BoxAllocator;
    let bbbbbbs = [Tree::node("ccc"), Tree::node("dd")];
    let ffffs = [Tree::node("gg"), Tree::node("hhh"), Tree::node("ii")];
    let aaas = [
        Tree::node_with_forest("bbbbbb", &bbbbbbs),
        Tree::node("eee"),
        Tree::node_with_forest("ffff", &ffffs),
    ];
    let example = Tree::node_with_forest("aaaa", &aaas);

    let err_msg = "<buffer is not a utf-8 encoded string>";

    // try writing to stdout
    {
        print!("\nwriting to stdout directly:\n");
        let mut out = io::stdout();
        example.pretty::<_, ()>(&allocator).1.render(70, &mut out)
        // try writing to memory
    }
    .and_then(|()| {
        print!("\nwriting to string then printing:\n");
        let mut mem = Vec::new();
        example
            .pretty::<_, ()>(&allocator)
            .1
            .render(70, &mut mem)
            // print to console from memory
            .map(|()| {
                let res = std::str::from_utf8(&mem).unwrap_or(err_msg);
                println!("{}", res)
            })
        // print an error if anything failed
    })
    .unwrap_or_else(|err| println!("error: {}", err));

    //let f1: fol::Formula = "forall Y (exists Z (exists I$ J$ (Z = I$ + J$ and Y = I$ and J$ = 1) and q(Z)) -> r(Y))".parse().unwrap();
    //let f2: fol::Formula = "forall Y (q(Y) -> exists Z (exists I$ J$ (Z = I$ - J$ and Y = I$ and J$ = 1) and r(Z)))".parse().unwrap();
    //let f3: fol::Formula = "forall Y( exists Z (exists I$ J$ (Z = I$ - J$ and Y = I$ and J$ = 1) and q(Y) -> r(Z)))".parse().unwrap();

    //println!("tff(con1, conjecture, {}).", Format(&f3));

    match Arguments::parse().command {
        Command::Translate { with, input, simplify } => {
            let content = read_to_string(&input)
                .with_context(|| format!("could not read file `{}`", input.display()))?;

            match with {
                Translation::Gamma => {
                    let theory = match input.extension() {
                        Some(extension) => match extension.to_str() {
                            Some(ext) => match ext {
                                "lp" => {
                                    let program: asp::Program = content.parse().with_context(|| format!("could not parse file `{}`", input.display()))?;
                                    tau_star(program)
                                },
                                "spec" => {
                                    let theory: fol::Theory = content.parse().with_context(|| format!("could not parse file `{}`", input.display()))?;
                                    theory
                                },
                                _ => todo!(),
                            },
                            None => todo!(),
                        },
                        None => todo!(),
                    };

                    let theory = gamma(theory);

                    if simplify {
                        let simple = ht_simplifications::simplify_theory(theory, true);
                        println!("{simple}");
                    } else {
                        println!("{theory}");
                    } 
                }

                Translation::TauStar => {
                    let program: asp::Program = content
                        .parse()
                        .with_context(|| format!("could not parse file `{}`", input.display()))?;

                    let theory = tau_star(program);

                    if simplify {
                        let simple = ht_simplifications::simplify_theory(theory, false);
                        println!("{simple}");
                    } else {
                        println!("{theory}");
                    } 
                }
                Translation::Completion => {
                    let theory = match input.extension() {
                        Some(extension) => match extension.to_str() {
                            Some(ext) => match ext {
                                "lp" => {
                                    let program: asp::Program = content.parse().with_context(|| format!("could not parse file `{}`", input.display()))?;
                                    tau_star(program)
                                },
                                "spec" => {
                                    let theory: fol::Theory = content.parse().with_context(|| format!("could not parse file `{}`", input.display()))?;
                                    theory
                                },
                                _ => todo!(),
                            },
                            None => todo!(),
                        },
                        None => todo!(),
                    };
                    
                    match completion(&theory) {
                        Some(completion) => {
                            if simplify {
                                let simple = ht_simplifications::simplify_theory(completion, true);
                                println!("{simple}");
                            } else {
                                println!("{completion}");
                            } 
                        }
                        None => {
                            println!("Not a completable theory.")
                        }
                    }
                }
                Translation::Simplify => {
                    let theory: fol::Theory = content
                        .parse()
                        .with_context(|| format!("could not parse file `{}`", input.display()))?;

                    let simple = ht_simplifications::simplify_theory(theory, true);

                    println!("{simple}");
                }
            }

            Ok(())
        }
        Command::Verify {
            with,
            program,
            specification,
            user_guide,
            lemmas,
            cores,
            break_equivalences,
            parallel,
            simplify,
        } => {
            verify(
                with,
                program,
                specification,
                user_guide,
                lemmas,
                cores,
                break_equivalences,
                parallel,
                simplify,
            )?;
            Ok(())
        }
        Command::VerifyAlt {
            with,
            directory,
            cores,
            break_equivalences,
            parallel,
            simplify,
        } => {
            let mut programs: Vec<&PathBuf> = vec![];
            let mut specs: Vec<&PathBuf> = vec![];
            let mut user_guides: Vec<&PathBuf> = vec![];
            let mut lemmas: Vec<&PathBuf> = vec![];

            // TODO - unpack and handle errors in files result
            let files = match collect_files(directory) {
                core::result::Result::Ok(f) => f,
                Err(e) => {
                    println!("Error! {e}");
                    vec![]
                }
            };
            for f in files.iter() {
                match f.extension() {
                    Some(extension) => match extension.to_str().unwrap() {
                        "lp" => {
                            if programs.is_empty() {
                                programs.push(f);
                            } else {
                                specs.push(f);
                            }
                        }
                        "spec" => {
                            if HELP.is_match(&f.clone().into_os_string().into_string().unwrap()) {
                                lemmas.push(f);
                            } else {
                                specs.push(f);
                            }
                        }
                        "ug" => {
                            user_guides.push(f);
                        }
                        _ => {
                            println!("Unexpected file! Ignoring {:?}", f);
                        }
                    },
                    None => {
                        println!("Encountered a file with an unexpected extension: {:?}", f);
                    }
                }
            }

            assert!(programs.len() == 1);
            assert!(specs.len() == 1);
            assert!(user_guides.len() == 1);
            assert!(lemmas.len() < 2);

            println!("Treating {:?} as the program...", programs[0]);
            println!("Treating {:?} as the specification...", specs[0]);
            println!("Treating {:?} as the user guide...", user_guides[0]);
            if lemmas.len() > 0 {
                println!("Treating {:?} as the lemmas...", lemmas[0]);
            }

            if lemmas.len() > 0 {
                verify(
                    with,
                    programs[0].to_path_buf(),
                    specs[0].to_path_buf(),
                    user_guides[0].to_path_buf(),
                    Some(lemmas[0].to_path_buf()),
                    cores,
                    break_equivalences,
                    parallel,
                    simplify,
                )?;
            } else {
                verify(
                    with,
                    programs[0].to_path_buf(),
                    specs[0].to_path_buf(),
                    user_guides[0].to_path_buf(),
                    None,
                    cores,
                    break_equivalences,
                    parallel,
                    simplify,
                )?;
            }
            Ok(())
        }
    }
}
