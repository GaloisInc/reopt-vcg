
#include <fcntl.h>
#include <stdio.h>
#include <unistd.h>

#include "runtime/apply.h"
#include "runtime/io.h"

using namespace lean;

static obj_res set_io_error_errno(obj_arg r) {
    object *msg = mk_string(strerror(errno));
    return set_io_error(r, msg);
}

////////////////////////////////////////////////////////////////////////
// IO operations

namespace galois {
namespace io {
namespace prim {        
namespace handle {
    
// handles are implemented as boxed scalars
static size_t
from_lean_handle(obj_arg n) { return unbox(n); }

static obj_res
to_lean_handle(size_t n) { return box(n); }
    
// constant handle.mk (s : @& String) (m : Mode) (bin : Bool := false) : IO handle := default _
// It looks like lean will pass simple sum types as uint8s, hence mode and bin below.
obj_res
mk(b_obj_arg s, uint8 mode, uint8 bin, obj_arg w) {
    size_t hdl;
    std::string filename = string_to_std(s);
    // FIXME: we should maybe take oflag as an arg instead of mode, or
    // set O_CREAT.  For now this avoids setting the mode (permissions) param
    int oflag = 0;

    // Lean doesn't export symbolic names for these (it really
    // should), so we guess that they are represented in order of
    // declaration.
    switch (mode) {
    case 0: oflag = O_RDONLY; break;
    case 1: oflag = O_WRONLY; break;
    case 2: oflag = O_RDWR;   break;
    case 3: oflag = O_APPEND; break;
    default: lean_unreachable();
    }

    hdl = open(filename.c_str(), oflag);
    if (hdl == -1) {
        return set_io_error_errno(w);
    }
    
    return set_io_result(w, to_lean_handle(hdl));
}
    
obj_res
do_read(b_obj_arg hdl_obj, obj_arg n_obj, obj_arg r) {
    int hdl      = (int) from_lean_handle(hdl_obj);

    // FIXME: asserts that n_obj is a scalar -- should we fail more gracefully?
    uint64 sz         = nat2uint64(n_obj);
    object *bytes_obj = alloc_sarray(1, sz, sz);
    uint8 *bytes      = sarray_cptr<uint8>(bytes_obj);

    ssize_t nread = read(hdl, bytes, sz);
    if (nread == -1) {
        dec(bytes_obj);
        return set_io_error_errno(r);
    }
    
    sarray_set_size(bytes_obj, nread);
    
    return set_io_result(r, bytes_obj);
}

obj_res
do_write(b_obj_arg hdl_obj, b_obj_arg bytes_obj, obj_arg r) {
    int hdl      = (int) from_lean_handle(hdl_obj);
    size_t sz    = (size_t) sarray_size(bytes_obj);
    uint8 *bytes = sarray_cptr<uint8>(bytes_obj);

    while(sz > 0) {
        ssize_t nwritten = write(hdl, bytes, sz);
        if (nwritten == -1) {
            return set_io_error_errno(r);
        }

        bytes += nwritten;
        sz    -= nwritten;
    }

    return r; // FIXME: do we need to add the Unit result?
}
    
obj_res
do_close(b_obj_arg hdl_obj, obj_arg r) {
    int hdl      = (int) from_lean_handle(hdl_obj);
    if (close(hdl) == -1) {
        return set_io_error_errno(r);
    }
    return r; // FIXME: Unit result?    
}

obj_res
do_lseek(b_obj_arg hdl_obj, obj_arg off_obj, uint8 whence, obj_arg r) {
    int hdl      = (int) from_lean_handle(hdl_obj);
    int64 off    = int2int64(off_obj);
    
    off_t res = lseek(hdl, off, whence);
    if (res == -1) {
        return set_io_error_errno(r);
    }
    return set_io_result(r, mk_nat_obj((uint64) res));
}
    
}
}
}
}
