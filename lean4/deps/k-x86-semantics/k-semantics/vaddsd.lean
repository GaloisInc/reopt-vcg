def vaddsd1 : instruction :=
  definst "vaddsd" $ do
    pattern fun (v_2705 : reg (bv 128)) (v_2706 : reg (bv 128)) (v_2707 : reg (bv 128)) => do
      v_4966 <- getRegister v_2706;
      v_4970 <- getRegister v_2705;
      setRegister (lhs.of_reg v_2707) (concat (extract v_4966 0 64) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4966 64 128) 53 11) (MInt2Float (extract v_4970 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2697 : Mem) (v_2700 : reg (bv 128)) (v_2701 : reg (bv 128)) => do
      v_9259 <- getRegister v_2700;
      v_9263 <- evaluateAddress v_2697;
      v_9264 <- load v_9263 8;
      setRegister (lhs.of_reg v_2701) (concat (extract v_9259 0 64) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9259 64 128) 53 11) (MInt2Float v_9264 53 11)) 64));
      pure ()
    pat_end
