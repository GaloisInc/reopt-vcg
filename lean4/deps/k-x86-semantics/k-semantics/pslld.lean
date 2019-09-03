def pslld1 : instruction :=
  definst "pslld" $ do
    pattern fun (v_2956 : imm int) (v_2955 : reg (bv 128)) => do
      v_7745 <- eval (handleImmediateWithSignExtend v_2956 8 8);
      v_7748 <- getRegister v_2955;
      v_7749 <- eval (extract v_7748 0 32);
      v_7751 <- eval (uvalueMInt (concat (expression.bv_nat 24 0) v_7745));
      v_7755 <- eval (extract v_7748 32 64);
      v_7759 <- eval (extract v_7748 64 96);
      v_7763 <- eval (extract v_7748 96 128);
      setRegister (lhs.of_reg v_2955) (mux (ugt (concat (expression.bv_nat 56 0) v_7745) (expression.bv_nat 64 31)) (expression.bv_nat 128 0) (concat (extract (shl v_7749 v_7751) 0 (bitwidthMInt v_7749)) (concat (extract (shl v_7755 v_7751) 0 (bitwidthMInt v_7755)) (concat (extract (shl v_7759 v_7751) 0 (bitwidthMInt v_7759)) (extract (shl v_7763 v_7751) 0 (bitwidthMInt v_7763))))));
      pure ()
    pat_end;
    pattern fun (v_2964 : reg (bv 128)) (v_2965 : reg (bv 128)) => do
      v_7776 <- getRegister v_2964;
      v_7779 <- getRegister v_2965;
      v_7780 <- eval (extract v_7779 0 32);
      v_7782 <- eval (uvalueMInt (extract v_7776 96 128));
      v_7786 <- eval (extract v_7779 32 64);
      v_7790 <- eval (extract v_7779 64 96);
      v_7794 <- eval (extract v_7779 96 128);
      setRegister (lhs.of_reg v_2965) (mux (ugt (extract v_7776 64 128) (expression.bv_nat 64 31)) (expression.bv_nat 128 0) (concat (extract (shl v_7780 v_7782) 0 (bitwidthMInt v_7780)) (concat (extract (shl v_7786 v_7782) 0 (bitwidthMInt v_7786)) (concat (extract (shl v_7790 v_7782) 0 (bitwidthMInt v_7790)) (extract (shl v_7794 v_7782) 0 (bitwidthMInt v_7794))))));
      pure ()
    pat_end;
    pattern fun (v_2959 : Mem) (v_2960 : reg (bv 128)) => do
      v_14952 <- evaluateAddress v_2959;
      v_14953 <- load v_14952 16;
      v_14956 <- getRegister v_2960;
      v_14957 <- eval (extract v_14956 0 32);
      v_14959 <- eval (uvalueMInt (extract v_14953 96 128));
      v_14963 <- eval (extract v_14956 32 64);
      v_14967 <- eval (extract v_14956 64 96);
      v_14971 <- eval (extract v_14956 96 128);
      setRegister (lhs.of_reg v_2960) (mux (ugt (extract v_14953 64 128) (expression.bv_nat 64 31)) (expression.bv_nat 128 0) (concat (extract (shl v_14957 v_14959) 0 (bitwidthMInt v_14957)) (concat (extract (shl v_14963 v_14959) 0 (bitwidthMInt v_14963)) (concat (extract (shl v_14967 v_14959) 0 (bitwidthMInt v_14967)) (extract (shl v_14971 v_14959) 0 (bitwidthMInt v_14971))))));
      pure ()
    pat_end
