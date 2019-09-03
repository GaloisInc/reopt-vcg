def vrcpss1 : instruction :=
  definst "vrcpss" $ do
    pattern fun (v_2806 : reg (bv 128)) (v_2807 : reg (bv 128)) (v_2808 : reg (bv 128)) => do
      v_6652 <- getRegister v_2807;
      v_6654 <- getRegister v_2806;
      v_6655 <- eval (extract v_6654 96 128);
      setRegister (lhs.of_reg v_2808) (concat (extract v_6652 0 96) (Float2MInt (_/Float__FLOAT 1e+00 (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6655 0 1)) (uvalueMInt (extract v_6655 1 9)) (uvalueMInt (extract v_6655 9 32)))) 32));
      pure ()
    pat_end;
    pattern fun (v_2801 : Mem) (v_2802 : reg (bv 128)) (v_2803 : reg (bv 128)) => do
      v_13037 <- getRegister v_2802;
      v_13039 <- evaluateAddress v_2801;
      v_13040 <- load v_13039 4;
      setRegister (lhs.of_reg v_2803) (concat (extract v_13037 0 96) (Float2MInt (_/Float__FLOAT 1e+00 (MIntToFloatImpl 24 8 (uvalueMInt (extract v_13040 0 1)) (uvalueMInt (extract v_13040 1 9)) (uvalueMInt (extract v_13040 9 32)))) 32));
      pure ()
    pat_end
