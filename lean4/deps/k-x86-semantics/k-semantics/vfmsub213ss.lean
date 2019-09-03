def vfmsub213ss1 : instruction :=
  definst "vfmsub213ss" $ do
    pattern fun (v_2882 : reg (bv 128)) (v_2883 : reg (bv 128)) (v_2884 : reg (bv 128)) => do
      v_8359 <- getRegister v_2884;
      v_8361 <- getRegister v_2883;
      v_8362 <- eval (extract v_8361 96 128);
      v_8370 <- eval (extract v_8359 96 128);
      v_8379 <- getRegister v_2882;
      v_8380 <- eval (extract v_8379 96 128);
      setRegister (lhs.of_reg v_2884) (concat (extract v_8359 0 96) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8362 0 1)) (uvalueMInt (extract v_8362 1 9)) (uvalueMInt (extract v_8362 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8370 0 1)) (uvalueMInt (extract v_8370 1 9)) (uvalueMInt (extract v_8370 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8380 0 1)) (uvalueMInt (extract v_8380 1 9)) (uvalueMInt (extract v_8380 9 32)))) 32));
      pure ()
    pat_end;
    pattern fun (v_2879 : Mem) (v_2877 : reg (bv 128)) (v_2878 : reg (bv 128)) => do
      v_19135 <- getRegister v_2878;
      v_19137 <- getRegister v_2877;
      v_19138 <- eval (extract v_19137 96 128);
      v_19146 <- eval (extract v_19135 96 128);
      v_19155 <- evaluateAddress v_2879;
      v_19156 <- load v_19155 4;
      setRegister (lhs.of_reg v_2878) (concat (extract v_19135 0 96) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_19138 0 1)) (uvalueMInt (extract v_19138 1 9)) (uvalueMInt (extract v_19138 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_19146 0 1)) (uvalueMInt (extract v_19146 1 9)) (uvalueMInt (extract v_19146 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_19156 0 1)) (uvalueMInt (extract v_19156 1 9)) (uvalueMInt (extract v_19156 9 32)))) 32));
      pure ()
    pat_end
