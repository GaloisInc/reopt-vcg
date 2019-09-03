def mulxl1 : instruction :=
  definst "mulxl" $ do
    pattern fun (v_2801 : reg (bv 32)) (v_2802 : reg (bv 32)) (v_2803 : reg (bv 32)) => do
      v_4411 <- getRegister rdx;
      v_4414 <- getRegister v_2801;
      v_4416 <- eval (mul (concat (expression.bv_nat 32 0) (extract v_4411 32 64)) (concat (expression.bv_nat 32 0) v_4414));
      setRegister (lhs.of_reg v_2802) (extract v_4416 32 64);
      setRegister (lhs.of_reg v_2803) (extract v_4416 0 32);
      pure ()
    pat_end;
    pattern fun (v_2791 : Mem) (v_2792 : reg (bv 32)) (v_2793 : reg (bv 32)) => do
      v_9145 <- evaluateAddress v_2791;
      v_9148 <- load v_9145 4;
      v_9150 <- eval (mul (concat (expression.bv_nat 32 0) (extract v_9145 32 64)) (concat (expression.bv_nat 32 0) v_9148));
      setRegister (lhs.of_reg v_2792) (extract v_9150 32 64);
      setRegister (lhs.of_reg v_2793) (extract v_9150 0 32);
      pure ()
    pat_end
