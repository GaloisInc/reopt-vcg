def vfnmadd132sd1 : instruction :=
  definst "vfnmadd132sd" $ do
    pattern fun (v_3122 : reg (bv 128)) (v_3123 : reg (bv 128)) (v_3124 : reg (bv 128)) => do
      v_6896 <- getRegister v_3124;
      v_6899 <- getRegister v_3123;
      v_6901 <- getRegister v_3122;
      setRegister (lhs.of_reg v_3124) (concat (extract v_6896 0 64) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_6896 64 128) (extract v_6899 64 128) (extract v_6901 64 128)));
      pure ()
    pat_end;
    pattern fun (v_3119 : Mem) (v_3117 : reg (bv 128)) (v_3118 : reg (bv 128)) => do
      v_12645 <- getRegister v_3118;
      v_12648 <- getRegister v_3117;
      v_12650 <- evaluateAddress v_3119;
      v_12651 <- load v_12650 8;
      setRegister (lhs.of_reg v_3118) (concat (extract v_12645 0 64) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_12645 64 128) (extract v_12648 64 128) v_12651));
      pure ()
    pat_end
