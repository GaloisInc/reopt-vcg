def subsd1 : instruction :=
  definst "subsd" $ do
    pattern fun (v_3314 : reg (bv 128)) (v_3315 : reg (bv 128)) => do
      v_6060 <- getRegister v_3315;
      v_6064 <- getRegister v_3314;
      setRegister (lhs.of_reg v_3315) (concat (extract v_6060 0 64) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_6060 64 128) 53 11) (MInt2Float (extract v_6064 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_3310 : Mem) (v_3311 : reg (bv 128)) => do
      v_8762 <- getRegister v_3311;
      v_8766 <- evaluateAddress v_3310;
      v_8767 <- load v_8766 8;
      setRegister (lhs.of_reg v_3311) (concat (extract v_8762 0 64) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_8762 64 128) 53 11) (MInt2Float v_8767 53 11)) 64));
      pure ()
    pat_end
