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

	public void AddPolicy(string path, string rego)
	{
	    var pathBytes = Encoding.UTF8.GetBytes(path);
	    var regoBytes = Encoding.UTF8.GetBytes(rego);
	    
	    unsafe
	    {
		fixed (byte* pathPtr = pathBytes)
		{
		    fixed(byte* regoPtr = regoBytes)
		    {
			CheckAndDropResult(RegorusFFI.API.regorus_engine_add_policy(E, pathPtr, regoPtr));
		    }
		}		
	    }
	}

	public void AddPolicyFromFile(string path)
	{
	    var pathBytes = Encoding.UTF8.GetBytes(path);
	    
	    unsafe
	    {
		fixed (byte* pathPtr = pathBytes)
		{
		    CheckAndDropResult(RegorusFFI.API.regorus_engine_add_policy_from_file(E, pathPtr));
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

	    var resultJson = "";
	    unsafe
	    {
		fixed (byte* queryPtr = queryBytes)
		{
		    var result = RegorusFFI.API.regorus_engine_eval_query(E, queryPtr);
		    if (result.status == RegorusFFI.RegorusStatus.RegorusStatusOk) {
			if (result.output is not null) {
			    resultJson = System.Runtime.InteropServices.Marshal.PtrToStringUTF8((IntPtr)result.output);
			}
			RegorusFFI.API.regorus_result_drop(result);
		    } else {
			CheckAndDropResult(result);
		    }
		    
		}		
	    }
	    if (resultJson is not null) {
		return resultJson;
	    } else {
		return "";
	    }
	}
	
	~Engine()
	{
	    unsafe
	    {
		RegorusFFI.API.regorus_engine_drop(E);
	    }
	}

	
	void CheckAndDropResult(RegorusFFI.RegorusResult result)
	{
	    if (result.status != RegorusFFI.RegorusStatus.RegorusStatusOk) {
		unsafe {
		    var message = System.Runtime.InteropServices.Marshal.PtrToStringUTF8((IntPtr)result.error_message);
		    var ex = new Exception(message);
		    RegorusFFI.API.regorus_result_drop(result);
		    throw ex;
		}
	    }
	    RegorusFFI.API.regorus_result_drop(result);		    
	}

    }
}
