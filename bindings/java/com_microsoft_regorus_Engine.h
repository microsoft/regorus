/* DO NOT EDIT THIS FILE - it is machine generated */
#include <jni.h>
/* Header for class com_microsoft_regorus_Engine */

#ifndef _Included_com_microsoft_regorus_Engine
#define _Included_com_microsoft_regorus_Engine
#ifdef __cplusplus
extern "C" {
#endif
/*
 * Class:     com_microsoft_regorus_Engine
 * Method:    nativeNewEngine
 * Signature: ()J
 */
JNIEXPORT jlong JNICALL Java_com_microsoft_regorus_Engine_nativeNewEngine
  (JNIEnv *, jclass);

/*
 * Class:     com_microsoft_regorus_Engine
 * Method:    nativeAddPolicy
 * Signature: (JLjava/lang/String;Ljava/lang/String;)V
 */
JNIEXPORT void JNICALL Java_com_microsoft_regorus_Engine_nativeAddPolicy
  (JNIEnv *, jclass, jlong, jstring, jstring);

/*
 * Class:     com_microsoft_regorus_Engine
 * Method:    nativeAddPolicyFromFile
 * Signature: (JLjava/lang/String;)V
 */
JNIEXPORT void JNICALL Java_com_microsoft_regorus_Engine_nativeAddPolicyFromFile
  (JNIEnv *, jclass, jlong, jstring);

/*
 * Class:     com_microsoft_regorus_Engine
 * Method:    nativeClearData
 * Signature: (J)V
 */
JNIEXPORT void JNICALL Java_com_microsoft_regorus_Engine_nativeClearData
  (JNIEnv *, jclass, jlong);

/*
 * Class:     com_microsoft_regorus_Engine
 * Method:    nativeAddDataJson
 * Signature: (JLjava/lang/String;)V
 */
JNIEXPORT void JNICALL Java_com_microsoft_regorus_Engine_nativeAddDataJson
  (JNIEnv *, jclass, jlong, jstring);

/*
 * Class:     com_microsoft_regorus_Engine
 * Method:    nativeAddDataJsonFromFile
 * Signature: (JLjava/lang/String;)V
 */
JNIEXPORT void JNICALL Java_com_microsoft_regorus_Engine_nativeAddDataJsonFromFile
  (JNIEnv *, jclass, jlong, jstring);

/*
 * Class:     com_microsoft_regorus_Engine
 * Method:    nativeSetInputJson
 * Signature: (JLjava/lang/String;)V
 */
JNIEXPORT void JNICALL Java_com_microsoft_regorus_Engine_nativeSetInputJson
  (JNIEnv *, jclass, jlong, jstring);

/*
 * Class:     com_microsoft_regorus_Engine
 * Method:    nativeSetInputJsonFromFile
 * Signature: (JLjava/lang/String;)V
 */
JNIEXPORT void JNICALL Java_com_microsoft_regorus_Engine_nativeSetInputJsonFromFile
  (JNIEnv *, jclass, jlong, jstring);

/*
 * Class:     com_microsoft_regorus_Engine
 * Method:    nativeEvalQuery
 * Signature: (JLjava/lang/String;)Ljava/lang/String;
 */
JNIEXPORT jstring JNICALL Java_com_microsoft_regorus_Engine_nativeEvalQuery
  (JNIEnv *, jclass, jlong, jstring);

/*
 * Class:     com_microsoft_regorus_Engine
 * Method:    nativeDestroyEngine
 * Signature: (J)V
 */
JNIEXPORT void JNICALL Java_com_microsoft_regorus_Engine_nativeDestroyEngine
  (JNIEnv *, jclass, jlong);

#ifdef __cplusplus
}
#endif
#endif
