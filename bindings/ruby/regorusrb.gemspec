# frozen_string_literal: true

require_relative "lib/regorus/version"

Gem::Specification.new do |spec|
  spec.name = "regorusrb"
  spec.version = Regorus::VERSION
  spec.authors = ["David Marshall"]

  spec.summary = "Ruby bindings for Regorus - a fast, lightweight Rego interpreter written in Rust"
  spec.homepage = "https://github.com/microsoft/regorus/blob/main/bindings/ruby"
  spec.license = "MIT"
  spec.required_ruby_version = ">= 3.0.0"
  spec.required_rubygems_version = ">= 3.3.11"

  spec.metadata["allowed_push_host"] = "TODO: Set to your gem server 'https://example.com'"

  spec.metadata["homepage_uri"] = spec.homepage
  spec.metadata["source_code_uri"] = spec.homepage
  spec.metadata["changelog_uri"] = "#{spec.homepage}/blob/main/bindings/ruby/CHANGELOG.md"
  spec.metadata["rubygems_mfa_required"] = "true"

  spec.files = Dir["lib/*.rb", "lib/regorus/*.rb", "ext/**/*.{rs,rb,lock,toml}", "Cargo.{lock,toml}", "LICENSE.txt", "README.md"]

  spec.bindir = "exe"
  spec.executables = spec.files.grep(%r{\Aexe/}) { |f| File.basename(f) }
  spec.require_paths = ["lib"]
  spec.extensions = ["ext/regorusrb/extconf.rb"]
  spec.add_dependency "rb_sys", "~> 0.9.91"
end
