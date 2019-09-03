def vfmadd231sd1 : instruction :=
  definst "vfmadd231sd" $ do
    pattern fun (v_2607 : reg (bv 128)) (v_2608 : reg (bv 128)) (v_2609 : reg (bv 128)) => do
      v_5552 <- getRegister v_2609;
      v_5554 <- getRegister v_2608;
      v_5555 <- eval (extract v_5554 64 128);
      v_5563 <- getRegister v_2607;
      v_5564 <- eval (extract v_5563 64 128);
      v_5573 <- eval (extract v_5552 64 128);
      setRegister (lhs.of_reg v_2609) (concat (extract v_5552 0 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_5555 0 1)) (uvalueMInt (extract v_5555 1 12)) (uvalueMInt (extract v_5555 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_5564 0 1)) (uvalueMInt (extract v_5564 1 12)) (uvalueMInt (extract v_5564 12 64)))) (MInt2Float (Float2MInt (_-Float__FLOAT -0e+00 (MIntToFloatImpl 53 11 (uvalueMInt (extract v_5573 0 1)) (uvalueMInt (extract v_5573 1 12)) (uvalueMInt (extract v_5573 12 64)))) 64) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2604 : Mem) (v_2602 : reg (bv 128)) (v_2603 : reg (bv 128)) => do
      v_16433 <- getRegister v_2603;
      v_16435 <- getRegister v_2602;
      v_16436 <- eval (extract v_16435 64 128);
      v_16444 <- evaluateAddress v_2604;
      v_16445 <- load v_16444 8;
      v_16454 <- eval (extract v_16433 64 128);
      setRegister (lhs.of_reg v_2603) (concat (extract v_16433 0 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_16436 0 1)) (uvalueMInt (extract v_16436 1 12)) (uvalueMInt (extract v_16436 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_16445 0 1)) (uvalueMInt (extract v_16445 1 12)) (uvalueMInt (extract v_16445 12 64)))) (MInt2Float (Float2MInt (_-Float__FLOAT -0e+00 (MIntToFloatImpl 53 11 (uvalueMInt (extract v_16454 0 1)) (uvalueMInt (extract v_16454 1 12)) (uvalueMInt (extract v_16454 12 64)))) 64) 53 11)) 64));
      pure ()
    pat_end
