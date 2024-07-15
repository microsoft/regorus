using System.Text;

namespace Regorus
{
    public class Exception : System.Exception
    {
	public Exception(string? message) : base(message) {}
    }

    public class Engine : ICloneable
    {
	unsafe private RegorusFFI.RegorusEngine* E;
	public Engine()
	{
	    unsafe
	    {
		E = RegorusFFI.API.regorus_engine_new();
	    }
	}

	public object Clone()
	{
	    var clone = (Engine)this.MemberwiseClone();
	    unsafe
	    {
		clone.E = RegorusFFI.API.regorus_engine_clone(E);
	    }
	    return clone;

	}

	public string AddPolicy(string path, string rego)
	{
	    var pathBytes = Encoding.UTF8.GetBytes(path);
	    var regoBytes = Encoding.UTF8.GetBytes(rego);

	    unsafe
	    {
		fixed (byte* pathPtr = pathBytes)
		{
		    fixed(byte* regoPtr = regoBytes)
		    {
			return CheckAndDropResult(RegorusFFI.API.regorus_engine_add_policy(E, pathPtr, regoPtr));
		    }
		}
	    }
	}

	public string AddPolicyFromFile(string path)
	{
	    var pathBytes = Encoding.UTF8.GetBytes(path);

	    unsafe
	    {
		fixed (byte* pathPtr = pathBytes)
		{
		    return CheckAndDropResult(RegorusFFI.API.regorus_engine_add_policy_from_file(E, pathPtr));
		}
	    }
	}

	public void AddDataJson(string data)
	{
	    var dataBytes = Encoding.UTF8.GetBytes(data);

	    unsafe
	    {
		fixed (byte* dataPtr = dataBytes)
		{
		    CheckAndDropResult(RegorusFFI.API.regorus_engine_add_data_json(E, dataPtr));
		}
	    }
	}

	public void AddDataFromJsonFile(string path)
	{
	    var pathBytes = Encoding.UTF8.GetBytes(path);

	    unsafe
	    {
		fixed (byte* pathPtr = pathBytes)
		{
		    CheckAndDropResult(RegorusFFI.API.regorus_engine_add_data_from_json_file(E, pathPtr));
		}
	    }
	}

	public void SetInputJson(string input)
	{
	    var inputBytes = Encoding.UTF8.GetBytes(input);

	    unsafe
	    {
		fixed (byte* inputPtr = inputBytes)
		{
		    CheckAndDropResult(RegorusFFI.API.regorus_engine_set_input_json(E, inputPtr));
		}
	    }
	}

	public void SetInputFromJsonFile(string path)
	{
	    var pathBytes = Encoding.UTF8.GetBytes(path);

	    unsafe
	    {
		fixed (byte* pathPtr = pathBytes)
		{
		    CheckAndDropResult(RegorusFFI.API.regorus_engine_set_input_from_json_file(E, pathPtr));
		}
	    }
	}

	public string EvalQuery(string query)
	{
	    var queryBytes = Encoding.UTF8.GetBytes(query);

	    unsafe
	    {
		fixed (byte* queryPtr = queryBytes)
		{
		    return CheckAndDropResult(RegorusFFI.API.regorus_engine_eval_query(E, queryPtr));
		}
	    }
	}

	public string EvalRule(string rule)
	{
	    var ruleBytes = Encoding.UTF8.GetBytes(rule);

	    unsafe
	    {
		fixed (byte* rulePtr = ruleBytes)
		{
		    return CheckAndDropResult(RegorusFFI.API.regorus_engine_eval_query(E, rulePtr));
		}
	    }
	}
	
	public void SetEnableCoverage(bool enable)
	{
	    unsafe
	    {
		CheckAndDropResult(RegorusFFI.API.regorus_engine_set_enable_coverage(E, enable));
	    }
	}
	
	public void ClearCoverageData()
	{
	    unsafe
	    {
		CheckAndDropResult(RegorusFFI.API.regorus_engine_clear_coverage_data(E));
	    }
	}
	
	public string GetCoverageReport()
	{
	    unsafe
	    {
		return CheckAndDropResult(RegorusFFI.API.regorus_engine_get_coverage_report(E));
	    }
	}
	
	public string GetCoverageReportPretty()
	{
	    unsafe
	    {
		return CheckAndDropResult(RegorusFFI.API.regorus_engine_get_coverage_report_pretty(E));
	    }
	}
	
	public void SetGatherPrints(bool enable)
	{
	    unsafe
	    {
		CheckAndDropResult(RegorusFFI.API.regorus_engine_set_gather_prints(E, enable));
	    }
	}
	
	public string TakePrints()
	{
	    unsafe
	    {
		return CheckAndDropResult(RegorusFFI.API.regorus_engine_take_prints(E));
	    }
	}
	
	~Engine()
	{
	    unsafe
	    {
		RegorusFFI.API.regorus_engine_drop(E);
	    }
	}


	string CheckAndDropResult(RegorusFFI.RegorusResult result)
	{
	    if (result.status != RegorusFFI.RegorusStatus.RegorusStatusOk) {
		unsafe {
		    var message = System.Runtime.InteropServices.Marshal.PtrToStringUTF8((IntPtr)result.error_message);
		    var ex = new Exception(message);
		    RegorusFFI.API.regorus_result_drop(result);
		    throw ex;
		}
	    }

	    var resultString = "";
	    unsafe
	    {
		if (result.output is not null) {
		    resultString = System.Runtime.InteropServices.Marshal.PtrToStringUTF8((IntPtr)result.output);
		}
		RegorusFFI.API.regorus_result_drop(result);
	    }
	    return resultString;
	}

    }
}
