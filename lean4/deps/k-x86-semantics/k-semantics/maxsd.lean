def maxsd1 : instruction :=
  definst "maxsd" $ do
    pattern fun (v_3082 : reg (bv 128)) (v_3083 : reg (bv 128)) => do
      v_6074 <- getRegister v_3083;
      v_6076 <- eval (extract v_6074 64 128);
      v_6077 <- getRegister v_3082;
      v_6078 <- eval (extract v_6077 64 128);
      setRegister (lhs.of_reg v_3083) (concat (extract v_6074 0 64) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_double v_6076 v_6078) (expression.bv_nat 1 1)) v_6076 v_6078));
      pure ()
    pat_end;
    pattern fun (v_3076 : Mem) (v_3078 : reg (bv 128)) => do
      v_9814 <- getRegister v_3078;
      v_9816 <- eval (extract v_9814 64 128);
      v_9817 <- evaluateAddress v_3076;
      v_9818 <- load v_9817 8;
      setRegister (lhs.of_reg v_3078) (concat (extract v_9814 0 64) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_double v_9816 v_9818) (expression.bv_nat 1 1)) v_9816 v_9818));
      pure ()
    pat_end
