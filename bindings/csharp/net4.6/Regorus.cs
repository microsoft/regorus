//-----------------------------------------------------------------------
// <copyright file="Regorus.cs" company="Microsoft">
//    Copyright (c)2012 Microsoft. All rights reserved.
// </copyright>
// <summary>
//    Contains code for the Regorus Policy Engine base class.
// </summary>
//-----------------------------------------------------------------------


using System;
using System.Text;
using System.IO;
using System.Threading;

namespace Microsoft.WindowsAzure.Regorus.IaaS
{

	public class PolicyEngine : ICloneable, IDisposable
	{
	unsafe private RegorusFFI.RegorusEngine* E;
	
	public PolicyEngine()
	{
		unsafe
	    {
		E = RegorusFFI.API.regorus_engine_new();
	    }
	}


	public void Dispose()
	{
		unsafe
		{
			if (E != null)
			{
				RegorusFFI.API.regorus_engine_drop(E);
				// to avoid Dispose() being called multiple times by mistake.
				E = null;
			}

		}

	}

	public object Clone()
	{
	    var clone = (PolicyEngine)this.MemberwiseClone();
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
	
	public void AddPolicyFromPath(string path)
	{
		if (!Directory.Exists(path))
		{
			return;
		}

		string[] regoFiles = Directory.GetFiles(path, "*.rego", SearchOption.AllDirectories);
		foreach (string file in regoFiles)
		{
			AddPolicyFromFile(file);
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
			if (result.output != null) {
			    resultJson = System.Runtime.InteropServices.Marshal.PtrToStringAnsi((IntPtr)result.output);
			}
			RegorusFFI.API.regorus_result_drop(result);
		    } else {
			CheckAndDropResult(result);
		    }
		    
		}		
	    }
	    if (resultJson != null) {
		return resultJson;
	    } else {
		return "";
	    }
	}
	
	void CheckAndDropResult(RegorusFFI.RegorusResult result)
	{
	    if (result.status != RegorusFFI.RegorusStatus.RegorusStatusOk) {
		unsafe {
		    var message = System.Runtime.InteropServices.Marshal.PtrToStringAnsi((IntPtr)result.error_message);
		    var ex = new Exception(message);
		    RegorusFFI.API.regorus_result_drop(result);
		    throw ex;
		}
	    }
	    RegorusFFI.API.regorus_result_drop(result);		    
	}

    }
}
