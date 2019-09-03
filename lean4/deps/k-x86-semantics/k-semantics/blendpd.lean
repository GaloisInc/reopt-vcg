def blendpd1 : instruction :=
  definst "blendpd" $ do
    pattern fun (v_2928 : imm int) (v_2930 : reg (bv 128)) (v_2931 : reg (bv 128)) => do
      v_5942 <- eval (handleImmediateWithSignExtend v_2928 8 8);
      v_5945 <- getRegister v_2931;
      v_5947 <- getRegister v_2930;
      setRegister (lhs.of_reg v_2931) (concat (mux (eq (extract v_5942 6 7) (expression.bv_nat 1 0)) (extract v_5945 0 64) (extract v_5947 0 64)) (mux (eq (extract v_5942 7 8) (expression.bv_nat 1 0)) (extract v_5945 64 128) (extract v_5947 64 128)));
      pure ()
    pat_end;
    pattern fun (v_2924 : imm int) (v_2923 : Mem) (v_2925 : reg (bv 128)) => do
      v_9791 <- eval (handleImmediateWithSignExtend v_2924 8 8);
      v_9794 <- getRegister v_2925;
      v_9796 <- evaluateAddress v_2923;
      v_9797 <- load v_9796 16;
      setRegister (lhs.of_reg v_2925) (concat (mux (eq (extract v_9791 6 7) (expression.bv_nat 1 0)) (extract v_9794 0 64) (extract v_9797 0 64)) (mux (eq (extract v_9791 7 8) (expression.bv_nat 1 0)) (extract v_9794 64 128) (extract v_9797 64 128)));
      pure ()
    pat_end
