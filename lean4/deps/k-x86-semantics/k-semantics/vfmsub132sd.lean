def vfmsub132sd1 : instruction :=
  definst "vfmsub132sd" $ do
    pattern fun (v_2805 : reg (bv 128)) (v_2806 : reg (bv 128)) (v_2807 : reg (bv 128)) => do
      v_7706 <- getRegister v_2807;
      v_7708 <- eval (extract v_7706 64 128);
      v_7716 <- getRegister v_2805;
      v_7717 <- eval (extract v_7716 64 128);
      v_7726 <- getRegister v_2806;
      v_7727 <- eval (extract v_7726 64 128);
      setRegister (lhs.of_reg v_2807) (concat (extract v_7706 0 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_7708 0 1)) (uvalueMInt (extract v_7708 1 12)) (uvalueMInt (extract v_7708 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_7717 0 1)) (uvalueMInt (extract v_7717 1 12)) (uvalueMInt (extract v_7717 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_7727 0 1)) (uvalueMInt (extract v_7727 1 12)) (uvalueMInt (extract v_7727 12 64)))) 64));
      pure ()
    pat_end;
    pattern fun (v_2802 : Mem) (v_2800 : reg (bv 128)) (v_2801 : reg (bv 128)) => do
      v_18513 <- getRegister v_2801;
      v_18515 <- eval (extract v_18513 64 128);
      v_18523 <- evaluateAddress v_2802;
      v_18524 <- load v_18523 8;
      v_18533 <- getRegister v_2800;
      v_18534 <- eval (extract v_18533 64 128);
      setRegister (lhs.of_reg v_2801) (concat (extract v_18513 0 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_18515 0 1)) (uvalueMInt (extract v_18515 1 12)) (uvalueMInt (extract v_18515 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_18524 0 1)) (uvalueMInt (extract v_18524 1 12)) (uvalueMInt (extract v_18524 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_18534 0 1)) (uvalueMInt (extract v_18534 1 12)) (uvalueMInt (extract v_18534 12 64)))) 64));
      pure ()
    pat_end
