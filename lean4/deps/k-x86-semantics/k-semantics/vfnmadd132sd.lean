def vfnmadd132sd1 : instruction :=
  definst "vfnmadd132sd" $ do
    pattern fun (v_3211 : reg (bv 128)) (v_3212 : reg (bv 128)) (v_3213 : reg (bv 128)) => do
      v_6990 <- getRegister v_3213;
      v_6993 <- getRegister v_3212;
      v_6995 <- getRegister v_3211;
      setRegister (lhs.of_reg v_3213) (concat (extract v_6990 0 64) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_6990 64 128) (extract v_6993 64 128) (extract v_6995 64 128)));
      pure ()
    pat_end;
    pattern fun (v_3208 : Mem) (v_3206 : reg (bv 128)) (v_3207 : reg (bv 128)) => do
      v_12756 <- getRegister v_3207;
      v_12759 <- getRegister v_3206;
      v_12761 <- evaluateAddress v_3208;
      v_12762 <- load v_12761 8;
      setRegister (lhs.of_reg v_3207) (concat (extract v_12756 0 64) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_12756 64 128) (extract v_12759 64 128) v_12762));
      pure ()
    pat_end
