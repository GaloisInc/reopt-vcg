def vfmsub231sd1 : instruction :=
  definst "vfmsub231sd" $ do
    pattern fun (v_2937 : reg (bv 128)) (v_2938 : reg (bv 128)) (v_2939 : reg (bv 128)) => do
      v_8933 <- getRegister v_2939;
      v_8935 <- getRegister v_2938;
      v_8936 <- eval (extract v_8935 64 128);
      v_8944 <- getRegister v_2937;
      v_8945 <- eval (extract v_8944 64 128);
      v_8954 <- eval (extract v_8933 64 128);
      setRegister (lhs.of_reg v_2939) (concat (extract v_8933 0 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_8936 0 1)) (uvalueMInt (extract v_8936 1 12)) (uvalueMInt (extract v_8936 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_8945 0 1)) (uvalueMInt (extract v_8945 1 12)) (uvalueMInt (extract v_8945 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_8954 0 1)) (uvalueMInt (extract v_8954 1 12)) (uvalueMInt (extract v_8954 12 64)))) 64));
      pure ()
    pat_end;
    pattern fun (v_2934 : Mem) (v_2932 : reg (bv 128)) (v_2933 : reg (bv 128)) => do
      v_19688 <- getRegister v_2933;
      v_19690 <- getRegister v_2932;
      v_19691 <- eval (extract v_19690 64 128);
      v_19699 <- evaluateAddress v_2934;
      v_19700 <- load v_19699 8;
      v_19709 <- eval (extract v_19688 64 128);
      setRegister (lhs.of_reg v_2933) (concat (extract v_19688 0 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_19691 0 1)) (uvalueMInt (extract v_19691 1 12)) (uvalueMInt (extract v_19691 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_19700 0 1)) (uvalueMInt (extract v_19700 1 12)) (uvalueMInt (extract v_19700 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_19709 0 1)) (uvalueMInt (extract v_19709 1 12)) (uvalueMInt (extract v_19709 12 64)))) 64));
      pure ()
    pat_end
