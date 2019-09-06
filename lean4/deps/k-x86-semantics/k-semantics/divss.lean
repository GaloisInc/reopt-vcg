def divss1 : instruction :=
  definst "divss" $ do
    pattern fun (v_2850 : reg (bv 128)) (v_2851 : reg (bv 128)) => do
      v_4629 <- getRegister v_2851;
      v_4633 <- getRegister v_2850;
      setRegister (lhs.of_reg v_2851) (concat (extract v_4629 0 96) (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_4629 96 128) 24 8) (MInt2Float (extract v_4633 96 128) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_2846 : Mem) (v_2847 : reg (bv 128)) => do
      v_8136 <- getRegister v_2847;
      v_8140 <- evaluateAddress v_2846;
      v_8141 <- load v_8140 4;
      setRegister (lhs.of_reg v_2847) (concat (extract v_8136 0 96) (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_8136 96 128) 24 8) (MInt2Float v_8141 24 8)) 32));
      pure ()
    pat_end
