def mulss1 : instruction :=
  definst "mulss" $ do
    pattern fun (v_2762 : reg (bv 128)) (v_2763 : reg (bv 128)) => do
      v_4254 <- getRegister v_2763;
      v_4258 <- getRegister v_2762;
      setRegister (lhs.of_reg v_2763) (concat (extract v_4254 0 96) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_4254 96 128) 24 8) (MInt2Float (extract v_4258 96 128) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_2757 : Mem) (v_2758 : reg (bv 128)) => do
      v_9033 <- getRegister v_2758;
      v_9037 <- evaluateAddress v_2757;
      v_9038 <- load v_9037 4;
      setRegister (lhs.of_reg v_2758) (concat (extract v_9033 0 96) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_9033 96 128) 24 8) (MInt2Float v_9038 24 8)) 32));
      pure ()
    pat_end
