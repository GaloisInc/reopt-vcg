def addss1 : instruction :=
  definst "addss" $ do
    pattern fun (v_2650 : reg (bv 128)) (v_2651 : reg (bv 128)) => do
      v_4933 <- getRegister v_2651;
      v_4937 <- getRegister v_2650;
      setRegister (lhs.of_reg v_2651) (concat (extract v_4933 0 96) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4933 96 128) 24 8) (MInt2Float (extract v_4937 96 128) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_2645 : Mem) (v_2646 : reg (bv 128)) => do
      v_9195 <- getRegister v_2646;
      v_9199 <- evaluateAddress v_2645;
      v_9200 <- load v_9199 4;
      setRegister (lhs.of_reg v_2646) (concat (extract v_9195 0 96) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9195 96 128) 24 8) (MInt2Float v_9200 24 8)) 32));
      pure ()
    pat_end
