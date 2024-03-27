#[allow(unused)]
use std::hint::black_box;

use criterion::{criterion_group, criterion_main, Criterion};

use tests::generate::Generate;
use tests::models::*;
#[allow(unused)]
use tests::utils;

fn criterion_benchmark(c: &mut Criterion) {
    let mut rng = tests::rng();

    macro_rules! for_each {
        ($name:ident, $call:ident) => {{
            #[allow(unused)]
            macro_rules! inner {
                ($framework:ident) => {{
                    tests::if_supported! {
                        $framework, $name, {
                            $call!($framework)
                        }
                    }
                }};
            }

            tests::feature_matrix!(inner);
        }};
    }

    macro_rules! group {
        ($group_name:expr, $name:ident, $it:ident) => {{
            #[allow(unused)]
            let mut g = c.benchmark_group($group_name);

            #[allow(unused)]
            macro_rules! inner {
                ($framework:ident) => {{
                    tests::if_supported! {
                        $framework, $name, {
                            g.bench_function(stringify!($framework), |b| $it!(b, $framework));
                        }
                    }
                }};
            }

            tests::feature_matrix!(inner);
        }};
    }

    macro_rules! setup {
        ($($name:ident, $ty:ty, $num:expr, $size_hint:expr),*) => {
            $({
                let mut values = Vec::<$ty>::new();
                Generate::generate_in(&mut rng, &mut values);

                macro_rules! check {
                    ($framework:ident) => {{
                        let mut frameworks = Vec::with_capacity(values.len());

                        for _ in &values {
                            frameworks.push(utils::$framework::new());
                        }

                        for (index, (value, framework)) in values.iter().zip(&mut frameworks).enumerate() {
                            let mut state = framework.state();
                            state.reset($size_hint, value);
                            let mut out = state.encode(value).unwrap();
                            let actual = out.decode::<$ty>().unwrap();
                            assert_eq!(actual, *value, "{} / {}: roundtrip encoding of value[{index}] should be equal", stringify!($framework), stringify!($name));
                        }
                    }}
                }

                for_each!($name, check);

                #[allow(unused)]
                macro_rules! it {
                    ($b:expr, $framework:ident) => {{
                        let mut frameworks = Vec::with_capacity(values.len());

                        for _ in &values {
                            frameworks.push(utils::$framework::new());
                        }

                        $b.iter(|| {
                            for (value, framework) in values.iter().zip(&mut frameworks) {
                                let mut state = framework.state();
                                state.reset($size_hint, value);
                                black_box(state.encode(value).unwrap());
                            }
                        });
                    }};
                }

                group!(concat!("enc/", stringify!($name)), $name, it);

                #[allow(unused)]
                macro_rules! it {
                    ($b:expr, $framework:ident) => {{
                        let mut frameworks = Vec::with_capacity(values.len());

                        for _ in &values {
                            frameworks.push(utils::$framework::new());
                        }

                        let mut states = Vec::with_capacity(values.len());

                        for framework in &mut frameworks {
                            states.push(framework.state());
                        }

                        let mut inputs = Vec::with_capacity(values.len());

                        for (value, state) in values.iter().zip(&mut states) {
                            state.reset($size_hint, value);
                            inputs.push(state.encode(value).unwrap());
                        }

                        $b.iter(move || {
                            for data in &mut inputs {
                                black_box(data.decode::<$ty>().unwrap());
                            }
                        });
                    }};
                }

                group!(concat!("dec/", stringify!($name)), $name, it);

                #[allow(unused)]
                macro_rules! it {
                    ($b:expr, $framework:ident) => {{
                        let mut frameworks = Vec::with_capacity(values.len());

                        for _ in &values {
                            frameworks.push(utils::$framework::new());
                        }

                        $b.iter(|| {
                            for (value, framework) in values.iter().zip(&mut frameworks) {
                                let mut state = framework.state();
                                state.reset($size_hint, value);
                                let mut out = black_box(state.encode(value).unwrap());
                                let actual = black_box(out.decode::<$ty>().unwrap());
                                debug_assert_eq!(actual, *value);
                                black_box(actual);
                            }
                        });
                    }};
                }

                #[cfg(not(feature = "no-rt"))]
                group!(concat!("rt/", stringify!($name)), $name, it);
            })*
        };
    }

    tests::types!(setup);
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
