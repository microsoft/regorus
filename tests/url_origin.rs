// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![cfg(all(feature = "std", feature = "urlquery"))]

use url::Url;

#[test]
fn blob_origins_do_not_recurse_into_nested_urls() {
    std::thread::Builder::new()
        .stack_size(2 * 1024 * 1024)
        .spawn(|| {
            let nested = format!("{}https://example.com/", "blob:".repeat(10_000));
            assert!(!Url::parse(&nested).unwrap().origin().is_tuple());

            for input in ["blob:blob:https://example.com/", "blob:ws://example.com/"] {
                assert!(!Url::parse(input).unwrap().origin().is_tuple(), "{input}");
            }
            assert_eq!(
                Url::parse("blob:https://example.com/")
                    .unwrap()
                    .origin()
                    .ascii_serialization(),
                "https://example.com"
            );
        })
        .unwrap()
        .join()
        .unwrap();
}
