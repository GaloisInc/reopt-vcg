def sqrtps1 : instruction :=
  definst "sqrtps" $ do
    pattern fun (v_3129 : reg (bv 128)) (v_3130 : reg (bv 128)) => do
      v_6030 <- getRegister v_3129;
      setRegister (lhs.of_reg v_3130) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_6030 0 32)) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_6030 32 64)) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_6030 64 96)) (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_6030 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_3126 : Mem) (v_3125 : reg (bv 128)) => do
      v_9152 <- evaluateAddress v_3126;
      v_9153 <- load v_9152 16;
      setRegister (lhs.of_reg v_3125) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_9153 0 32)) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_9153 32 64)) (concat (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_9153 64 96)) (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_9153 96 128)))));
      pure ()
    pat_end
