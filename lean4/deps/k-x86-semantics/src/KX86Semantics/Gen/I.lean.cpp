
#define XSTR(x) #x
#define STR(x) XSTR(x)

namespace x86
namespace k-x86-semantics
namespace gen
    
#include STR(INSTRUCTION.lean)

end gen
end k-x86-semantics
end x86
