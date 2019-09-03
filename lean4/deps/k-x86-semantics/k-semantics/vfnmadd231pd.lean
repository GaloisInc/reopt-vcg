def vfnmadd231pd1 : instruction :=
  definst "vfnmadd231pd" $ do
    pattern fun (v_3210 : reg (bv 128)) (v_3211 : reg (bv 128)) (v_3212 : reg (bv 128)) => do
      v_7078 <- getRegister v_3211;
      v_7080 <- getRegister v_3212;
      v_7082 <- getRegister v_3210;
      setRegister (lhs.of_reg v_3212) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_7078 0 64) (extract v_7080 0 64) (extract v_7082 0 64)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_7078 64 128) (extract v_7080 64 128) (extract v_7082 64 128)));
      pure ()
    pat_end;
    pattern fun (v_3222 : reg (bv 256)) (v_3223 : reg (bv 256)) (v_3224 : reg (bv 256)) => do
      v_7096 <- getRegister v_3223;
      v_7098 <- getRegister v_3224;
      v_7100 <- getRegister v_3222;
      setRegister (lhs.of_reg v_3224) (concat (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_7096 0 64) (extract v_7098 0 64) (extract v_7100 0 64)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_7096 64 128) (extract v_7098 64 128) (extract v_7100 64 128))) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_7096 128 192) (extract v_7098 128 192) (extract v_7100 128 192)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_7096 192 256) (extract v_7098 192 256) (extract v_7100 192 256))));
      pure ()
    pat_end;
    pattern fun (v_3207 : Mem) (v_3205 : reg (bv 128)) (v_3206 : reg (bv 128)) => do
      v_12791 <- getRegister v_3205;
      v_12793 <- getRegister v_3206;
      v_12795 <- evaluateAddress v_3207;
      v_12796 <- load v_12795 16;
      setRegister (lhs.of_reg v_3206) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_12791 0 64) (extract v_12793 0 64) (extract v_12796 0 64)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_12791 64 128) (extract v_12793 64 128) (extract v_12796 64 128)));
      pure ()
    pat_end;
    pattern fun (v_3216 : Mem) (v_3217 : reg (bv 256)) (v_3218 : reg (bv 256)) => do
      v_12805 <- getRegister v_3217;
      v_12807 <- getRegister v_3218;
      v_12809 <- evaluateAddress v_3216;
      v_12810 <- load v_12809 32;
      setRegister (lhs.of_reg v_3218) (concat (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_12805 0 64) (extract v_12807 0 64) (extract v_12810 0 64)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_12805 64 128) (extract v_12807 64 128) (extract v_12810 64 128))) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_12805 128 192) (extract v_12807 128 192) (extract v_12810 128 192)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_12805 192 256) (extract v_12807 192 256) (extract v_12810 192 256))));
      pure ()
    pat_end
