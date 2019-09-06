def vfmsubadd132pd1 : instruction :=
  definst "vfmsubadd132pd" $ do
    pattern fun (v_3035 : reg (bv 128)) (v_3036 : reg (bv 128)) (v_3037 : reg (bv 128)) => do
      v_6247 <- getRegister v_3037;
      v_6250 <- getRegister v_3035;
      v_6254 <- getRegister v_3036;
      setRegister (lhs.of_reg v_3037) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6247 0 64) 53 11) (MInt2Float (extract v_6250 0 64) 53 11)) (MInt2Float (extract v_6254 0 64) 53 11)) 64) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_6247 64 128) (extract v_6254 64 128) (extract v_6250 64 128)));
      pure ()
    pat_end;
    pattern fun (v_3049 : reg (bv 256)) (v_3050 : reg (bv 256)) (v_3051 : reg (bv 256)) => do
      v_6270 <- getRegister v_3051;
      v_6273 <- getRegister v_3049;
      v_6277 <- getRegister v_3050;
      setRegister (lhs.of_reg v_3051) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6270 0 64) 53 11) (MInt2Float (extract v_6273 0 64) 53 11)) (MInt2Float (extract v_6277 0 64) 53 11)) 64) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_6270 64 128) (extract v_6277 64 128) (extract v_6273 64 128))) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6270 128 192) 53 11) (MInt2Float (extract v_6273 128 192) 53 11)) (MInt2Float (extract v_6277 128 192) 53 11)) 64) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_6270 192 256) (extract v_6277 192 256) (extract v_6273 192 256))));
      pure ()
    pat_end;
    pattern fun (v_3032 : Mem) (v_3030 : reg (bv 128)) (v_3031 : reg (bv 128)) => do
      v_12077 <- getRegister v_3031;
      v_12080 <- evaluateAddress v_3032;
      v_12081 <- load v_12080 16;
      v_12085 <- getRegister v_3030;
      setRegister (lhs.of_reg v_3031) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12077 0 64) 53 11) (MInt2Float (extract v_12081 0 64) 53 11)) (MInt2Float (extract v_12085 0 64) 53 11)) 64) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_12077 64 128) (extract v_12085 64 128) (extract v_12081 64 128)));
      pure ()
    pat_end;
    pattern fun (v_3041 : Mem) (v_3044 : reg (bv 256)) (v_3045 : reg (bv 256)) => do
      v_12096 <- getRegister v_3045;
      v_12099 <- evaluateAddress v_3041;
      v_12100 <- load v_12099 32;
      v_12104 <- getRegister v_3044;
      setRegister (lhs.of_reg v_3045) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12096 0 64) 53 11) (MInt2Float (extract v_12100 0 64) 53 11)) (MInt2Float (extract v_12104 0 64) 53 11)) 64) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_12096 64 128) (extract v_12104 64 128) (extract v_12100 64 128))) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12096 128 192) 53 11) (MInt2Float (extract v_12100 128 192) 53 11)) (MInt2Float (extract v_12104 128 192) 53 11)) 64) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_12096 192 256) (extract v_12104 192 256) (extract v_12100 192 256))));
      pure ()
    pat_end
