def cvtsi2ssq1 : instruction :=
  definst "cvtsi2ssq" $ do
    pattern fun (v_2591 : reg (bv 64)) (v_2593 : reg (bv 128)) => do
      v_4260 <- getRegister v_2593;
      v_4262 <- getRegister v_2591;
      setRegister (lhs.of_reg v_2593) (concat (extract v_4260 0 96) (Float2MInt (Int2Float (svalueMInt v_4262) 24 8) 32));
      pure ()
    pat_end;
    pattern fun (v_2586 : Mem) (v_2588 : reg (bv 128)) => do
      v_8474 <- getRegister v_2588;
      v_8476 <- evaluateAddress v_2586;
      v_8477 <- load v_8476 8;
      setRegister (lhs.of_reg v_2588) (concat (extract v_8474 0 96) (Float2MInt (Int2Float (svalueMInt v_8477) 24 8) 32));
      pure ()
    pat_end
