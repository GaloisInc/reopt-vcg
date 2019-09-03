def vfmadd213sd1 : instruction :=
  definst "vfmadd213sd" $ do
    pattern fun (v_2541 : reg (bv 128)) (v_2542 : reg (bv 128)) (v_2543 : reg (bv 128)) => do
      v_5026 <- getRegister v_2543;
      v_5028 <- getRegister v_2542;
      v_5029 <- eval (extract v_5028 64 128);
      v_5037 <- eval (extract v_5026 64 128);
      v_5046 <- getRegister v_2541;
      v_5047 <- eval (extract v_5046 64 128);
      setRegister (lhs.of_reg v_2543) (concat (extract v_5026 0 64) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_5029 0 1)) (uvalueMInt (extract v_5029 1 12)) (uvalueMInt (extract v_5029 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_5037 0 1)) (uvalueMInt (extract v_5037 1 12)) (uvalueMInt (extract v_5037 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_5047 0 1)) (uvalueMInt (extract v_5047 1 12)) (uvalueMInt (extract v_5047 12 64)))) 64));
      pure ()
    pat_end;
    pattern fun (v_2538 : Mem) (v_2536 : reg (bv 128)) (v_2537 : reg (bv 128)) => do
      v_15933 <- getRegister v_2537;
      v_15935 <- getRegister v_2536;
      v_15936 <- eval (extract v_15935 64 128);
      v_15944 <- eval (extract v_15933 64 128);
      v_15953 <- evaluateAddress v_2538;
      v_15954 <- load v_15953 8;
      setRegister (lhs.of_reg v_2537) (concat (extract v_15933 0 64) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_15936 0 1)) (uvalueMInt (extract v_15936 1 12)) (uvalueMInt (extract v_15936 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_15944 0 1)) (uvalueMInt (extract v_15944 1 12)) (uvalueMInt (extract v_15944 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_15954 0 1)) (uvalueMInt (extract v_15954 1 12)) (uvalueMInt (extract v_15954 12 64)))) 64));
      pure ()
    pat_end
