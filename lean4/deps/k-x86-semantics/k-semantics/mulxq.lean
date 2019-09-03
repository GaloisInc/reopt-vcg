def mulxq1 : instruction :=
  definst "mulxq" $ do
    pattern fun (v_2822 : reg (bv 64)) (v_2823 : reg (bv 64)) (v_2824 : reg (bv 64)) => do
      v_4431 <- getRegister rdx;
      v_4433 <- getRegister v_2822;
      v_4435 <- eval (mul (concat (expression.bv_nat 64 0) v_4431) (concat (expression.bv_nat 64 0) v_4433));
      setRegister (lhs.of_reg v_2823) (extract v_4435 64 128);
      setRegister (lhs.of_reg v_2824) (extract v_4435 0 64);
      pure ()
    pat_end;
    pattern fun (v_2812 : Mem) (v_2813 : reg (bv 64)) (v_2814 : reg (bv 64)) => do
      v_9156 <- evaluateAddress v_2812;
      v_9158 <- load v_9156 8;
      v_9160 <- eval (mul (concat (expression.bv_nat 64 0) v_9156) (concat (expression.bv_nat 64 0) v_9158));
      setRegister (lhs.of_reg v_2813) (extract v_9160 64 128);
      setRegister (lhs.of_reg v_2814) (extract v_9160 0 64);
      pure ()
    pat_end
