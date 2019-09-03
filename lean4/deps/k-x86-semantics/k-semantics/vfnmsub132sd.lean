def vfnmsub132sd1 : instruction :=
  definst "vfnmsub132sd" $ do
    pattern fun (v_3333 : reg (bv 128)) (v_3334 : reg (bv 128)) (v_3335 : reg (bv 128)) => do
      v_11587 <- getRegister v_3335;
      v_11589 <- eval (extract v_11587 64 128);
      v_11597 <- getRegister v_3333;
      v_11598 <- eval (extract v_11597 64 128);
      v_11608 <- getRegister v_3334;
      v_11609 <- eval (extract v_11608 64 128);
      setRegister (lhs.of_reg v_3335) (concat (extract v_11587 0 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_11589 0 1)) (uvalueMInt (extract v_11589 1 12)) (uvalueMInt (extract v_11589 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_11598 0 1)) (uvalueMInt (extract v_11598 1 12)) (uvalueMInt (extract v_11598 12 64))))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_11609 0 1)) (uvalueMInt (extract v_11609 1 12)) (uvalueMInt (extract v_11609 12 64)))) 64));
      pure ()
    pat_end;
    pattern fun (v_3330 : Mem) (v_3328 : reg (bv 128)) (v_3329 : reg (bv 128)) => do
      v_22190 <- getRegister v_3329;
      v_22192 <- eval (extract v_22190 64 128);
      v_22200 <- evaluateAddress v_3330;
      v_22201 <- load v_22200 8;
      v_22211 <- getRegister v_3328;
      v_22212 <- eval (extract v_22211 64 128);
      setRegister (lhs.of_reg v_3329) (concat (extract v_22190 0 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_22192 0 1)) (uvalueMInt (extract v_22192 1 12)) (uvalueMInt (extract v_22192 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_22201 0 1)) (uvalueMInt (extract v_22201 1 12)) (uvalueMInt (extract v_22201 12 64))))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_22212 0 1)) (uvalueMInt (extract v_22212 1 12)) (uvalueMInt (extract v_22212 12 64)))) 64));
      pure ()
    pat_end
