#include "CelBoolVar.h"


CelBoolVar::CelBoolVar(string &name) : CelIntVar(name, 0.0, 1.0) {
}

CelBoolVar::CelBoolVar(const char *namestr) : CelIntVar(namestr, 0.0, 1.0) {
}


CelBoolVar::CelBoolVar() : CelIntVar() {
}

CelBoolVar& CelBoolVar::operator= (const CelBoolVar other){
    *this = other;
    return *this;
}

CelBoolVar::~CelBoolVar(){
}


