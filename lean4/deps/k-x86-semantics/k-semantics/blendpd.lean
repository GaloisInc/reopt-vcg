def blendpd1 : instruction :=
  definst "blendpd" $ do
    pattern fun (v_2914 : imm int) (v_2917 : reg (bv 128)) (v_2918 : reg (bv 128)) => do
      v_5783 <- eval (handleImmediateWithSignExtend v_2914 8 8);
      v_5786 <- getRegister v_2918;
      v_5788 <- getRegister v_2917;
      setRegister (lhs.of_reg v_2918) (concat (mux (eq (extract v_5783 6 7) (expression.bv_nat 1 0)) (extract v_5786 0 64) (extract v_5788 0 64)) (mux (eq (extract v_5783 7 8) (expression.bv_nat 1 0)) (extract v_5786 64 128) (extract v_5788 64 128)));
      pure ()
    pat_end;
    pattern fun (v_2909 : imm int) (v_2911 : Mem) (v_2912 : reg (bv 128)) => do
      v_9499 <- eval (handleImmediateWithSignExtend v_2909 8 8);
      v_9502 <- getRegister v_2912;
      v_9504 <- evaluateAddress v_2911;
      v_9505 <- load v_9504 16;
      setRegister (lhs.of_reg v_2912) (concat (mux (eq (extract v_9499 6 7) (expression.bv_nat 1 0)) (extract v_9502 0 64) (extract v_9505 0 64)) (mux (eq (extract v_9499 7 8) (expression.bv_nat 1 0)) (extract v_9502 64 128) (extract v_9505 64 128)));
      pure ()
    pat_end
