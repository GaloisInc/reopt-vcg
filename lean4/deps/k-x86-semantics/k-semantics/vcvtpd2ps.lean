def vcvtpd2ps1 : instruction :=
  definst "vcvtpd2ps" $ do
    pattern fun (v_3069 : reg (bv 128)) (v_3070 : reg (bv 128)) => do
      v_6388 <- getRegister v_3069;
      v_6389 <- eval (extract v_6388 0 64);
      v_6399 <- eval (extract v_6388 64 128);
      setRegister (lhs.of_reg v_3070) (concat (expression.bv_nat 64 0) (concat (Float2MInt (roundFloat (MIntToFloatImpl 53 11 (uvalueMInt (extract v_6389 0 1)) (uvalueMInt (extract v_6389 1 12)) (uvalueMInt (extract v_6389 12 64))) 24 8) 32) (Float2MInt (roundFloat (MIntToFloatImpl 53 11 (uvalueMInt (extract v_6399 0 1)) (uvalueMInt (extract v_6399 1 12)) (uvalueMInt (extract v_6399 12 64))) 24 8) 32)));
      pure ()
    pat_end;
    pattern fun (v_3071 : reg (bv 256)) (v_3075 : reg (bv 128)) => do
      v_6412 <- getRegister v_3071;
      v_6413 <- eval (extract v_6412 0 64);
      v_6423 <- eval (extract v_6412 64 128);
      v_6433 <- eval (extract v_6412 128 192);
      v_6443 <- eval (extract v_6412 192 256);
      setRegister (lhs.of_reg v_3075) (concat (Float2MInt (roundFloat (MIntToFloatImpl 53 11 (uvalueMInt (extract v_6413 0 1)) (uvalueMInt (extract v_6413 1 12)) (uvalueMInt (extract v_6413 12 64))) 24 8) 32) (concat (Float2MInt (roundFloat (MIntToFloatImpl 53 11 (uvalueMInt (extract v_6423 0 1)) (uvalueMInt (extract v_6423 1 12)) (uvalueMInt (extract v_6423 12 64))) 24 8) 32) (concat (Float2MInt (roundFloat (MIntToFloatImpl 53 11 (uvalueMInt (extract v_6433 0 1)) (uvalueMInt (extract v_6433 1 12)) (uvalueMInt (extract v_6433 12 64))) 24 8) 32) (Float2MInt (roundFloat (MIntToFloatImpl 53 11 (uvalueMInt (extract v_6443 0 1)) (uvalueMInt (extract v_6443 1 12)) (uvalueMInt (extract v_6443 12 64))) 24 8) 32))));
      pure ()
    pat_end;
    pattern fun (v_3062 : Mem) (v_3065 : reg (bv 128)) => do
      v_11757 <- evaluateAddress v_3062;
      v_11758 <- load v_11757 16;
      v_11759 <- eval (extract v_11758 0 64);
      v_11769 <- eval (extract v_11758 64 128);
      setRegister (lhs.of_reg v_3065) (concat (expression.bv_nat 64 0) (concat (Float2MInt (roundFloat (MIntToFloatImpl 53 11 (uvalueMInt (extract v_11759 0 1)) (uvalueMInt (extract v_11759 1 12)) (uvalueMInt (extract v_11759 12 64))) 24 8) 32) (Float2MInt (roundFloat (MIntToFloatImpl 53 11 (uvalueMInt (extract v_11769 0 1)) (uvalueMInt (extract v_11769 1 12)) (uvalueMInt (extract v_11769 12 64))) 24 8) 32)));
      pure ()
    pat_end;
    pattern fun (v_3062 : Mem) (v_3065 : reg (bv 128)) => do
      v_11782 <- evaluateAddress v_3062;
      v_11783 <- load v_11782 16;
      v_11784 <- eval (extract v_11783 0 64);
      v_11794 <- eval (extract v_11783 64 128);
      v_11804 <- eval (extract v_11783 128 192);
      v_11814 <- eval (extract v_11783 192 256);
      setRegister (lhs.of_reg v_3065) (concat (Float2MInt (roundFloat (MIntToFloatImpl 53 11 (uvalueMInt (extract v_11784 0 1)) (uvalueMInt (extract v_11784 1 12)) (uvalueMInt (extract v_11784 12 64))) 24 8) 32) (concat (Float2MInt (roundFloat (MIntToFloatImpl 53 11 (uvalueMInt (extract v_11794 0 1)) (uvalueMInt (extract v_11794 1 12)) (uvalueMInt (extract v_11794 12 64))) 24 8) 32) (concat (Float2MInt (roundFloat (MIntToFloatImpl 53 11 (uvalueMInt (extract v_11804 0 1)) (uvalueMInt (extract v_11804 1 12)) (uvalueMInt (extract v_11804 12 64))) 24 8) 32) (Float2MInt (roundFloat (MIntToFloatImpl 53 11 (uvalueMInt (extract v_11814 0 1)) (uvalueMInt (extract v_11814 1 12)) (uvalueMInt (extract v_11814 12 64))) 24 8) 32))));
      pure ()
    pat_end;
    pattern fun (v_3062 : Mem) (v_3065 : reg (bv 128)) => do
      v_11828 <- evaluateAddress v_3062;
      v_11829 <- load v_11828 32;
      v_11830 <- eval (extract v_11829 0 64);
      v_11840 <- eval (extract v_11829 64 128);
      setRegister (lhs.of_reg v_3065) (concat (expression.bv_nat 64 0) (concat (Float2MInt (roundFloat (MIntToFloatImpl 53 11 (uvalueMInt (extract v_11830 0 1)) (uvalueMInt (extract v_11830 1 12)) (uvalueMInt (extract v_11830 12 64))) 24 8) 32) (Float2MInt (roundFloat (MIntToFloatImpl 53 11 (uvalueMInt (extract v_11840 0 1)) (uvalueMInt (extract v_11840 1 12)) (uvalueMInt (extract v_11840 12 64))) 24 8) 32)));
      pure ()
    pat_end;
    pattern fun (v_3062 : Mem) (v_3065 : reg (bv 128)) => do
      v_11853 <- evaluateAddress v_3062;
      v_11854 <- load v_11853 32;
      v_11855 <- eval (extract v_11854 0 64);
      v_11865 <- eval (extract v_11854 64 128);
      v_11875 <- eval (extract v_11854 128 192);
      v_11885 <- eval (extract v_11854 192 256);
      setRegister (lhs.of_reg v_3065) (concat (Float2MInt (roundFloat (MIntToFloatImpl 53 11 (uvalueMInt (extract v_11855 0 1)) (uvalueMInt (extract v_11855 1 12)) (uvalueMInt (extract v_11855 12 64))) 24 8) 32) (concat (Float2MInt (roundFloat (MIntToFloatImpl 53 11 (uvalueMInt (extract v_11865 0 1)) (uvalueMInt (extract v_11865 1 12)) (uvalueMInt (extract v_11865 12 64))) 24 8) 32) (concat (Float2MInt (roundFloat (MIntToFloatImpl 53 11 (uvalueMInt (extract v_11875 0 1)) (uvalueMInt (extract v_11875 1 12)) (uvalueMInt (extract v_11875 12 64))) 24 8) 32) (Float2MInt (roundFloat (MIntToFloatImpl 53 11 (uvalueMInt (extract v_11885 0 1)) (uvalueMInt (extract v_11885 1 12)) (uvalueMInt (extract v_11885 12 64))) 24 8) 32))));
      pure ()
    pat_end
