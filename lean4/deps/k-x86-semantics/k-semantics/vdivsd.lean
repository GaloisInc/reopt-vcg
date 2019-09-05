def vdivsd1 : instruction :=
  definst "vdivsd" $ do
    pattern fun (v_3455 : reg (bv 128)) (v_3456 : reg (bv 128)) (v_3457 : reg (bv 128)) => do
      v_6503 <- getRegister v_3456;
      v_6507 <- getRegister v_3455;
      setRegister (lhs.of_reg v_3457) (concat (extract v_6503 0 64) (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_6503 64 128) 53 11) (MInt2Float (extract v_6507 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_3449 : Mem) (v_3450 : reg (bv 128)) (v_3451 : reg (bv 128)) => do
      v_10499 <- getRegister v_3450;
      v_10503 <- evaluateAddress v_3449;
      v_10504 <- load v_10503 8;
      setRegister (lhs.of_reg v_3451) (concat (extract v_10499 0 64) (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_10499 64 128) 53 11) (MInt2Float v_10504 53 11)) 64));
      pure ()
    pat_end
