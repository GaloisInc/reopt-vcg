def vcvtps2pd1 : instruction :=
  definst "vcvtps2pd" $ do
    pattern fun (v_3119 : reg (bv 128)) (v_3120 : reg (bv 128)) => do
      v_6649 <- getRegister v_3119;
      v_6650 <- eval (extract v_6649 64 96);
      v_6660 <- eval (extract v_6649 96 128);
      setRegister (lhs.of_reg v_3120) (concat (Float2MInt (roundFloat (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6650 0 1)) (uvalueMInt (extract v_6650 1 9)) (uvalueMInt (extract v_6650 9 32))) 53 11) 64) (Float2MInt (roundFloat (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6660 0 1)) (uvalueMInt (extract v_6660 1 9)) (uvalueMInt (extract v_6660 9 32))) 53 11) 64));
      pure ()
    pat_end;
    pattern fun (v_3129 : reg (bv 128)) (v_3125 : reg (bv 256)) => do
      v_6676 <- getRegister v_3129;
      v_6677 <- eval (extract v_6676 0 32);
      v_6687 <- eval (extract v_6676 32 64);
      v_6697 <- eval (extract v_6676 64 96);
      v_6707 <- eval (extract v_6676 96 128);
      setRegister (lhs.of_reg v_3125) (concat (Float2MInt (roundFloat (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6677 0 1)) (uvalueMInt (extract v_6677 1 9)) (uvalueMInt (extract v_6677 9 32))) 53 11) 64) (concat (Float2MInt (roundFloat (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6687 0 1)) (uvalueMInt (extract v_6687 1 9)) (uvalueMInt (extract v_6687 9 32))) 53 11) 64) (concat (Float2MInt (roundFloat (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6697 0 1)) (uvalueMInt (extract v_6697 1 9)) (uvalueMInt (extract v_6697 9 32))) 53 11) 64) (Float2MInt (roundFloat (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6707 0 1)) (uvalueMInt (extract v_6707 1 9)) (uvalueMInt (extract v_6707 9 32))) 53 11) 64))));
      pure ()
    pat_end;
    pattern fun (v_3112 : Mem) (v_3115 : reg (bv 128)) => do
      v_12075 <- evaluateAddress v_3112;
      v_12076 <- load v_12075 8;
      v_12077 <- eval (extract v_12076 0 32);
      v_12087 <- eval (extract v_12076 32 64);
      setRegister (lhs.of_reg v_3115) (concat (Float2MInt (roundFloat (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12077 0 1)) (uvalueMInt (extract v_12077 1 9)) (uvalueMInt (extract v_12077 9 32))) 53 11) 64) (Float2MInt (roundFloat (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12087 0 1)) (uvalueMInt (extract v_12087 1 9)) (uvalueMInt (extract v_12087 9 32))) 53 11) 64));
      pure ()
    pat_end;
    pattern fun (v_3121 : Mem) (v_3122 : reg (bv 256)) => do
      v_12099 <- evaluateAddress v_3121;
      v_12100 <- load v_12099 16;
      v_12101 <- eval (extract v_12100 0 32);
      v_12111 <- eval (extract v_12100 32 64);
      v_12121 <- eval (extract v_12100 64 96);
      v_12131 <- eval (extract v_12100 96 128);
      setRegister (lhs.of_reg v_3122) (concat (Float2MInt (roundFloat (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12101 0 1)) (uvalueMInt (extract v_12101 1 9)) (uvalueMInt (extract v_12101 9 32))) 53 11) 64) (concat (Float2MInt (roundFloat (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12111 0 1)) (uvalueMInt (extract v_12111 1 9)) (uvalueMInt (extract v_12111 9 32))) 53 11) 64) (concat (Float2MInt (roundFloat (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12121 0 1)) (uvalueMInt (extract v_12121 1 9)) (uvalueMInt (extract v_12121 9 32))) 53 11) 64) (Float2MInt (roundFloat (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12131 0 1)) (uvalueMInt (extract v_12131 1 9)) (uvalueMInt (extract v_12131 9 32))) 53 11) 64))));
      pure ()
    pat_end
