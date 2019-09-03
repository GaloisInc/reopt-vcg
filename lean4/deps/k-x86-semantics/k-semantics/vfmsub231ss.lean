def vfmsub231ss1 : instruction :=
  definst "vfmsub231ss" $ do
    pattern fun (v_2948 : reg (bv 128)) (v_2949 : reg (bv 128)) (v_2950 : reg (bv 128)) => do
      v_8971 <- getRegister v_2950;
      v_8973 <- getRegister v_2949;
      v_8974 <- eval (extract v_8973 96 128);
      v_8982 <- getRegister v_2948;
      v_8983 <- eval (extract v_8982 96 128);
      v_8992 <- eval (extract v_8971 96 128);
      setRegister (lhs.of_reg v_2950) (concat (extract v_8971 0 96) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8974 0 1)) (uvalueMInt (extract v_8974 1 9)) (uvalueMInt (extract v_8974 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8983 0 1)) (uvalueMInt (extract v_8983 1 9)) (uvalueMInt (extract v_8983 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8992 0 1)) (uvalueMInt (extract v_8992 1 9)) (uvalueMInt (extract v_8992 9 32)))) 32));
      pure ()
    pat_end;
    pattern fun (v_2945 : Mem) (v_2943 : reg (bv 128)) (v_2944 : reg (bv 128)) => do
      v_19721 <- getRegister v_2944;
      v_19723 <- getRegister v_2943;
      v_19724 <- eval (extract v_19723 96 128);
      v_19732 <- evaluateAddress v_2945;
      v_19733 <- load v_19732 4;
      v_19742 <- eval (extract v_19721 96 128);
      setRegister (lhs.of_reg v_2944) (concat (extract v_19721 0 96) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_19724 0 1)) (uvalueMInt (extract v_19724 1 9)) (uvalueMInt (extract v_19724 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_19733 0 1)) (uvalueMInt (extract v_19733 1 9)) (uvalueMInt (extract v_19733 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_19742 0 1)) (uvalueMInt (extract v_19742 1 9)) (uvalueMInt (extract v_19742 9 32)))) 32));
      pure ()
    pat_end
