def minsd1 : instruction :=
  definst "minsd" $ do
    pattern fun (v_3118 : reg (bv 128)) (v_3119 : reg (bv 128)) => do
      v_6150 <- getRegister v_3119;
      v_6152 <- eval (extract v_6150 64 128);
      v_6153 <- getRegister v_3118;
      v_6154 <- eval (extract v_6153 64 128);
      setRegister (lhs.of_reg v_3119) (concat (extract v_6150 0 64) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double v_6152 v_6154) (expression.bv_nat 1 1)) v_6152 v_6154));
      pure ()
    pat_end;
    pattern fun (v_3112 : Mem) (v_3114 : reg (bv 128)) => do
      v_9876 <- getRegister v_3114;
      v_9878 <- eval (extract v_9876 64 128);
      v_9879 <- evaluateAddress v_3112;
      v_9880 <- load v_9879 8;
      setRegister (lhs.of_reg v_3114) (concat (extract v_9876 0 64) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double v_9878 v_9880) (expression.bv_nat 1 1)) v_9878 v_9880));
      pure ()
    pat_end
