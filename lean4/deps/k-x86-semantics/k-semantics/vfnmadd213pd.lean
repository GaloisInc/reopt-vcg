def vfnmadd213pd1 : instruction :=
  definst "vfnmadd213pd" $ do
    pattern fun (v_3233 : reg (bv 128)) (v_3234 : reg (bv 128)) (v_3235 : reg (bv 128)) => do
      v_7020 <- getRegister v_3234;
      v_7022 <- getRegister v_3233;
      v_7024 <- getRegister v_3235;
      setRegister (lhs.of_reg v_3235) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_7020 0 64) (extract v_7022 0 64) (extract v_7024 0 64)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_7020 64 128) (extract v_7022 64 128) (extract v_7024 64 128)));
      pure ()
    pat_end;
    pattern fun (v_3247 : reg (bv 256)) (v_3248 : reg (bv 256)) (v_3249 : reg (bv 256)) => do
      v_7038 <- getRegister v_3248;
      v_7040 <- getRegister v_3247;
      v_7042 <- getRegister v_3249;
      setRegister (lhs.of_reg v_3249) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_7038 0 64) (extract v_7040 0 64) (extract v_7042 0 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_7038 64 128) (extract v_7040 64 128) (extract v_7042 64 128)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_7038 128 192) (extract v_7040 128 192) (extract v_7042 128 192)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_7038 192 256) (extract v_7040 192 256) (extract v_7042 192 256)))));
      pure ()
    pat_end;
    pattern fun (v_3230 : Mem) (v_3228 : reg (bv 128)) (v_3229 : reg (bv 128)) => do
      v_12776 <- getRegister v_3228;
      v_12778 <- evaluateAddress v_3230;
      v_12779 <- load v_12778 16;
      v_12781 <- getRegister v_3229;
      setRegister (lhs.of_reg v_3229) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_12776 0 64) (extract v_12779 0 64) (extract v_12781 0 64)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_12776 64 128) (extract v_12779 64 128) (extract v_12781 64 128)));
      pure ()
    pat_end;
    pattern fun (v_3239 : Mem) (v_3242 : reg (bv 256)) (v_3243 : reg (bv 256)) => do
      v_12790 <- getRegister v_3242;
      v_12792 <- evaluateAddress v_3239;
      v_12793 <- load v_12792 32;
      v_12795 <- getRegister v_3243;
      setRegister (lhs.of_reg v_3243) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_12790 0 64) (extract v_12793 0 64) (extract v_12795 0 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_12790 64 128) (extract v_12793 64 128) (extract v_12795 64 128)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_12790 128 192) (extract v_12793 128 192) (extract v_12795 128 192)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_12790 192 256) (extract v_12793 192 256) (extract v_12795 192 256)))));
      pure ()
    pat_end
