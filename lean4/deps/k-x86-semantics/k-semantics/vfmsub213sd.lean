def vfmsub213sd1 : instruction :=
  definst "vfmsub213sd" $ do
    pattern fun (v_2871 : reg (bv 128)) (v_2872 : reg (bv 128)) (v_2873 : reg (bv 128)) => do
      v_8321 <- getRegister v_2873;
      v_8323 <- getRegister v_2872;
      v_8324 <- eval (extract v_8323 64 128);
      v_8332 <- eval (extract v_8321 64 128);
      v_8341 <- getRegister v_2871;
      v_8342 <- eval (extract v_8341 64 128);
      setRegister (lhs.of_reg v_2873) (concat (extract v_8321 0 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_8324 0 1)) (uvalueMInt (extract v_8324 1 12)) (uvalueMInt (extract v_8324 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_8332 0 1)) (uvalueMInt (extract v_8332 1 12)) (uvalueMInt (extract v_8332 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_8342 0 1)) (uvalueMInt (extract v_8342 1 12)) (uvalueMInt (extract v_8342 12 64)))) 64));
      pure ()
    pat_end;
    pattern fun (v_2868 : Mem) (v_2866 : reg (bv 128)) (v_2867 : reg (bv 128)) => do
      v_19102 <- getRegister v_2867;
      v_19104 <- getRegister v_2866;
      v_19105 <- eval (extract v_19104 64 128);
      v_19113 <- eval (extract v_19102 64 128);
      v_19122 <- evaluateAddress v_2868;
      v_19123 <- load v_19122 8;
      setRegister (lhs.of_reg v_2867) (concat (extract v_19102 0 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_19105 0 1)) (uvalueMInt (extract v_19105 1 12)) (uvalueMInt (extract v_19105 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_19113 0 1)) (uvalueMInt (extract v_19113 1 12)) (uvalueMInt (extract v_19113 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_19123 0 1)) (uvalueMInt (extract v_19123 1 12)) (uvalueMInt (extract v_19123 12 64)))) 64));
      pure ()
    pat_end
