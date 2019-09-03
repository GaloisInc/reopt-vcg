def maxps1 : instruction :=
  definst "maxps" $ do
    pattern fun (v_3060 : reg (bv 128)) (v_3061 : reg (bv 128)) => do
      v_5747 <- getRegister v_3061;
      v_5748 <- eval (extract v_5747 0 32);
      v_5749 <- getRegister v_3060;
      v_5750 <- eval (extract v_5749 0 32);
      v_5754 <- eval (extract v_5747 32 64);
      v_5755 <- eval (extract v_5749 32 64);
      v_5759 <- eval (extract v_5747 64 96);
      v_5760 <- eval (extract v_5749 64 96);
      v_5764 <- eval (extract v_5747 96 128);
      v_5765 <- eval (extract v_5749 96 128);
      setRegister (lhs.of_reg v_3061) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_5748 v_5750) (expression.bv_nat 1 1)) v_5748 v_5750) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_5754 v_5755) (expression.bv_nat 1 1)) v_5754 v_5755) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_5759 v_5760) (expression.bv_nat 1 1)) v_5759 v_5760) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_5764 v_5765) (expression.bv_nat 1 1)) v_5764 v_5765))));
      pure ()
    pat_end;
    pattern fun (v_3056 : Mem) (v_3057 : reg (bv 128)) => do
      v_9197 <- getRegister v_3057;
      v_9198 <- eval (extract v_9197 0 32);
      v_9199 <- evaluateAddress v_3056;
      v_9200 <- load v_9199 16;
      v_9201 <- eval (extract v_9200 0 32);
      v_9205 <- eval (extract v_9197 32 64);
      v_9206 <- eval (extract v_9200 32 64);
      v_9210 <- eval (extract v_9197 64 96);
      v_9211 <- eval (extract v_9200 64 96);
      v_9215 <- eval (extract v_9197 96 128);
      v_9216 <- eval (extract v_9200 96 128);
      setRegister (lhs.of_reg v_3057) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_9198 v_9201) (expression.bv_nat 1 1)) v_9198 v_9201) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_9205 v_9206) (expression.bv_nat 1 1)) v_9205 v_9206) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_9210 v_9211) (expression.bv_nat 1 1)) v_9210 v_9211) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_9215 v_9216) (expression.bv_nat 1 1)) v_9215 v_9216))));
      pure ()
    pat_end
