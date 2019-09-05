def vfmsubadd132pd1 : instruction :=
  definst "vfmsubadd132pd" $ do
    pattern fun (v_3011 : reg (bv 128)) (v_3012 : reg (bv 128)) (v_3013 : reg (bv 128)) => do
      v_6220 <- getRegister v_3013;
      v_6223 <- getRegister v_3011;
      v_6227 <- getRegister v_3012;
      setRegister (lhs.of_reg v_3013) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6220 0 64) 53 11) (MInt2Float (extract v_6223 0 64) 53 11)) (MInt2Float (extract v_6227 0 64) 53 11)) 64) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_6220 64 128) (extract v_6227 64 128) (extract v_6223 64 128)));
      pure ()
    pat_end;
    pattern fun (v_3021 : reg (bv 256)) (v_3022 : reg (bv 256)) (v_3023 : reg (bv 256)) => do
      v_6243 <- getRegister v_3023;
      v_6246 <- getRegister v_3021;
      v_6250 <- getRegister v_3022;
      setRegister (lhs.of_reg v_3023) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6243 0 64) 53 11) (MInt2Float (extract v_6246 0 64) 53 11)) (MInt2Float (extract v_6250 0 64) 53 11)) 64) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_6243 64 128) (extract v_6250 64 128) (extract v_6246 64 128))) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6243 128 192) 53 11) (MInt2Float (extract v_6246 128 192) 53 11)) (MInt2Float (extract v_6250 128 192) 53 11)) 64) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_6243 192 256) (extract v_6250 192 256) (extract v_6246 192 256))));
      pure ()
    pat_end;
    pattern fun (v_3005 : Mem) (v_3006 : reg (bv 128)) (v_3007 : reg (bv 128)) => do
      v_12050 <- getRegister v_3007;
      v_12053 <- evaluateAddress v_3005;
      v_12054 <- load v_12053 16;
      v_12058 <- getRegister v_3006;
      setRegister (lhs.of_reg v_3007) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12050 0 64) 53 11) (MInt2Float (extract v_12054 0 64) 53 11)) (MInt2Float (extract v_12058 0 64) 53 11)) 64) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_12050 64 128) (extract v_12058 64 128) (extract v_12054 64 128)));
      pure ()
    pat_end;
    pattern fun (v_3016 : Mem) (v_3017 : reg (bv 256)) (v_3018 : reg (bv 256)) => do
      v_12069 <- getRegister v_3018;
      v_12072 <- evaluateAddress v_3016;
      v_12073 <- load v_12072 32;
      v_12077 <- getRegister v_3017;
      setRegister (lhs.of_reg v_3018) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12069 0 64) 53 11) (MInt2Float (extract v_12073 0 64) 53 11)) (MInt2Float (extract v_12077 0 64) 53 11)) 64) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_12069 64 128) (extract v_12077 64 128) (extract v_12073 64 128))) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12069 128 192) 53 11) (MInt2Float (extract v_12073 128 192) 53 11)) (MInt2Float (extract v_12077 128 192) 53 11)) 64) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_12069 192 256) (extract v_12077 192 256) (extract v_12073 192 256))));
      pure ()
    pat_end
