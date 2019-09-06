def pshufd1 : instruction :=
  definst "pshufd" $ do
    pattern fun (v_2991 : imm int) (v_2992 : reg (bv 128)) (v_2993 : reg (bv 128)) => do
      v_7184 <- getRegister v_2992;
      v_7185 <- eval (handleImmediateWithSignExtend v_2991 8 8);
      setRegister (lhs.of_reg v_2993) (concat (extract (lshr v_7184 (extract (shl (concat (expression.bv_nat 126 0) (extract v_7185 0 2)) (expression.bv_nat 128 5)) 0 128)) 96 128) (concat (extract (lshr v_7184 (extract (shl (concat (expression.bv_nat 126 0) (extract v_7185 2 4)) (expression.bv_nat 128 5)) 0 128)) 96 128) (concat (extract (lshr v_7184 (extract (shl (concat (expression.bv_nat 126 0) (extract v_7185 4 6)) (expression.bv_nat 128 5)) 0 128)) 96 128) (extract (lshr v_7184 (extract (shl (concat (expression.bv_nat 126 0) (extract v_7185 6 8)) (expression.bv_nat 128 5)) 0 128)) 96 128))));
      pure ()
    pat_end;
    pattern fun (v_2987 : imm int) (v_2986 : Mem) (v_2988 : reg (bv 128)) => do
      v_13857 <- evaluateAddress v_2986;
      v_13858 <- load v_13857 16;
      v_13859 <- eval (handleImmediateWithSignExtend v_2987 8 8);
      setRegister (lhs.of_reg v_2988) (concat (extract (lshr v_13858 (extract (shl (concat (expression.bv_nat 126 0) (extract v_13859 0 2)) (expression.bv_nat 128 5)) 0 128)) 96 128) (concat (extract (lshr v_13858 (extract (shl (concat (expression.bv_nat 126 0) (extract v_13859 2 4)) (expression.bv_nat 128 5)) 0 128)) 96 128) (concat (extract (lshr v_13858 (extract (shl (concat (expression.bv_nat 126 0) (extract v_13859 4 6)) (expression.bv_nat 128 5)) 0 128)) 96 128) (extract (lshr v_13858 (extract (shl (concat (expression.bv_nat 126 0) (extract v_13859 6 8)) (expression.bv_nat 128 5)) 0 128)) 96 128))));
      pure ()
    pat_end
