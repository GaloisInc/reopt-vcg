def vfnmsub231ss1 : instruction :=
  definst "vfnmsub231ss" $ do
    pattern fun (v_3476 : reg (bv 128)) (v_3477 : reg (bv 128)) (v_3478 : reg (bv 128)) => do
      v_12903 <- getRegister v_3478;
      v_12905 <- getRegister v_3477;
      v_12906 <- eval (extract v_12905 96 128);
      v_12914 <- getRegister v_3476;
      v_12915 <- eval (extract v_12914 96 128);
      v_12925 <- eval (extract v_12903 96 128);
      setRegister (lhs.of_reg v_3478) (concat (extract v_12903 0 96) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12906 0 1)) (uvalueMInt (extract v_12906 1 9)) (uvalueMInt (extract v_12906 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12915 0 1)) (uvalueMInt (extract v_12915 1 9)) (uvalueMInt (extract v_12915 9 32))))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12925 0 1)) (uvalueMInt (extract v_12925 1 9)) (uvalueMInt (extract v_12925 9 32)))) 32));
      pure ()
    pat_end;
    pattern fun (v_3473 : Mem) (v_3471 : reg (bv 128)) (v_3472 : reg (bv 128)) => do
      v_23449 <- getRegister v_3472;
      v_23451 <- getRegister v_3471;
      v_23452 <- eval (extract v_23451 96 128);
      v_23460 <- evaluateAddress v_3473;
      v_23461 <- load v_23460 4;
      v_23471 <- eval (extract v_23449 96 128);
      setRegister (lhs.of_reg v_3472) (concat (extract v_23449 0 96) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_23452 0 1)) (uvalueMInt (extract v_23452 1 9)) (uvalueMInt (extract v_23452 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_23461 0 1)) (uvalueMInt (extract v_23461 1 9)) (uvalueMInt (extract v_23461 9 32))))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_23471 0 1)) (uvalueMInt (extract v_23471 1 9)) (uvalueMInt (extract v_23471 9 32)))) 32));
      pure ()
    pat_end
