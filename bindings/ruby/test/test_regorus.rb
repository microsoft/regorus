# frozen_string_literal: true

require "test_helper"
require "json"

class TestRegorus < Minitest::Test
  def example_policy
    <<~REGO
      package regorus_test
      is_manager {
          input.name == data.managers[_]
      }

      is_employee {
          input.name == data.employees[_]
      }
    REGO
  end

  def example_data
    {
      "managers" => ["Alice"],
      "employees" => ["Alice", "Bob"]
    }
  end

  def alice_input
    { "name" => "Alice" }
  end

  def test_that_it_has_a_version_number
    refute_nil ::Regorus::VERSION
  end

  def test_it_creates_an_engine
    assert_instance_of ::Regorus::Engine, ::Regorus::Engine.new
  end

  def test_it_implements_add_policy
    engine = ::Regorus::Engine.new

    assert_silent { engine.add_policy("example.rego", example_policy) }
  end

  def test_it_creates_new_objects_with_new
    refute_equal ::Regorus::Engine.new.object_id, ::Regorus::Engine.new.object_id
  end

  def test_sorting_engine_objects
    engine_array = [::Regorus::Engine.new, ::Regorus::Engine.new]
    assert_silent { engine_array.sort }
  end

  def test_it_implements_add_data
    engine = ::Regorus::Engine.new

    assert_silent { engine.add_data(example_data) }
  end

  def test_it_implements_add_data_json
    engine = ::Regorus::Engine.new

    assert_silent { engine.add_data_json(example_data.to_json) }
  end

  def test_it_implements_eval_query
    engine = ::Regorus::Engine.new
    engine.add_policy("regorus_test.rego", example_policy)
    engine.add_data(example_data)
    engine.set_input(alice_input)

    assert_equal alice_results, engine.eval_query("data.regorus_test")
  end

  def test_it_implements_eval_query_as_json
    engine = ::Regorus::Engine.new
    engine.add_policy("regorus_test.rego", example_policy)
    engine.add_data(example_data)
    engine.set_input(alice_input)

    assert_equal alice_results.to_json, engine.eval_query_as_json("data.regorus_test")
  end

  def test_it_creates_new_objects_with_clone
    engine = ::Regorus::Engine.new
    cloned_engine = engine.clone

    assert_instance_of ::Regorus::Engine, cloned_engine
    refute_equal engine.object_id, cloned_engine.object_id
  end

  def test_it_clones_state_when_engine_is_cloned
    engine = ::Regorus::Engine.new
    engine.add_policy("regorus_test.rego", example_policy)
    engine.add_data(example_data)
    engine.set_input(alice_input)

    cloned_engine = engine.clone

    assert_equal alice_results, cloned_engine.eval_query("data.regorus_test")
  end

  def alice_results
    {
      result: [
        {
          expressions: [
            {
              value: {
                "is_employee" => true,
                "is_manager" => true
              },
              text: "data.regorus_test",
              location: {
                row: 1,
                col: 1
              }
            }
          ]
        }
      ]
    }
  end
end
