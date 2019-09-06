def mulss1 : instruction :=
  definst "mulss" $ do
    pattern fun (v_2850 : reg (bv 128)) (v_2851 : reg (bv 128)) => do
      v_4341 <- getRegister v_2851;
      v_4345 <- getRegister v_2850;
      setRegister (lhs.of_reg v_2851) (concat (extract v_4341 0 96) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_4341 96 128) 24 8) (MInt2Float (extract v_4345 96 128) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_2846 : Mem) (v_2847 : reg (bv 128)) => do
      v_8900 <- getRegister v_2847;
      v_8904 <- evaluateAddress v_2846;
      v_8905 <- load v_8904 4;
      setRegister (lhs.of_reg v_2847) (concat (extract v_8900 0 96) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_8900 96 128) 24 8) (MInt2Float v_8905 24 8)) 32));
      pure ()
    pat_end
