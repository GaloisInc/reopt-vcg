def vaddss1 : instruction :=
  definst "vaddss" $ do
    pattern fun (v_2689 : reg (bv 128)) (v_2690 : reg (bv 128)) (v_2691 : reg (bv 128)) => do
      v_4955 <- getRegister v_2690;
      v_4959 <- getRegister v_2689;
      setRegister (lhs.of_reg v_2691) (concat (extract v_4955 0 96) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4955 96 128) 24 8) (MInt2Float (extract v_4959 96 128) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_2683 : Mem) (v_2684 : reg (bv 128)) (v_2685 : reg (bv 128)) => do
      v_9243 <- getRegister v_2684;
      v_9247 <- evaluateAddress v_2683;
      v_9248 <- load v_9247 4;
      setRegister (lhs.of_reg v_2685) (concat (extract v_9243 0 96) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9243 96 128) 24 8) (MInt2Float v_9248 24 8)) 32));
      pure ()
    pat_end
