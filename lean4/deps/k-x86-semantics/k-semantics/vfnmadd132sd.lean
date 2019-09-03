def vfnmadd132sd1 : instruction :=
  definst "vfnmadd132sd" $ do
    pattern fun (v_3135 : reg (bv 128)) (v_3136 : reg (bv 128)) (v_3137 : reg (bv 128)) => do
      v_10670 <- getRegister v_3137;
      v_10673 <- getRegister v_3136;
      v_10675 <- getRegister v_3135;
      setRegister (lhs.of_reg v_3137) (concat (extract v_10670 0 64) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_10670 64 128) (extract v_10673 64 128) (extract v_10675 64 128)));
      pure ()
    pat_end;
    pattern fun (v_3132 : Mem) (v_3130 : reg (bv 128)) (v_3131 : reg (bv 128)) => do
      v_21351 <- getRegister v_3131;
      v_21354 <- getRegister v_3130;
      v_21356 <- evaluateAddress v_3132;
      v_21357 <- load v_21356 8;
      setRegister (lhs.of_reg v_3131) (concat (extract v_21351 0 64) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_21351 64 128) (extract v_21354 64 128) v_21357));
      pure ()
    pat_end
