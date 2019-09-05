def shufps1 : instruction :=
  definst "shufps" $ do
    pattern fun (v_3112 : imm int) (v_3110 : reg (bv 128)) (v_3111 : reg (bv 128)) => do
      v_5980 <- eval (handleImmediateWithSignExtend v_3112 8 8);
      v_5982 <- eval (isBitSet v_5980 0);
      v_5983 <- getRegister v_3110;
      v_5984 <- eval (extract v_5983 0 32);
      v_5985 <- eval (extract v_5983 64 96);
      v_5987 <- eval (extract v_5983 32 64);
      v_5988 <- eval (extract v_5983 96 128);
      v_5992 <- eval (isBitSet v_5980 2);
      v_5997 <- eval (isBitSet v_5980 4);
      v_5998 <- getRegister v_3111;
      v_5999 <- eval (extract v_5998 0 32);
      v_6000 <- eval (extract v_5998 64 96);
      v_6002 <- eval (extract v_5998 32 64);
      v_6003 <- eval (extract v_5998 96 128);
      v_6007 <- eval (isBitSet v_5980 6);
      setRegister (lhs.of_reg v_3111) (concat (mux (isBitSet v_5980 1) (mux v_5982 v_5984 v_5985) (mux v_5982 v_5987 v_5988)) (concat (mux (isBitSet v_5980 3) (mux v_5992 v_5984 v_5985) (mux v_5992 v_5987 v_5988)) (concat (mux (isBitSet v_5980 5) (mux v_5997 v_5999 v_6000) (mux v_5997 v_6002 v_6003)) (mux (isBitSet v_5980 7) (mux v_6007 v_5999 v_6000) (mux v_6007 v_6002 v_6003)))));
      pure ()
    pat_end;
    pattern fun (v_3107 : imm int) (v_3106 : Mem) (v_3105 : reg (bv 128)) => do
      v_9108 <- eval (handleImmediateWithSignExtend v_3107 8 8);
      v_9110 <- eval (isBitSet v_9108 0);
      v_9111 <- evaluateAddress v_3106;
      v_9112 <- load v_9111 16;
      v_9113 <- eval (extract v_9112 0 32);
      v_9114 <- eval (extract v_9112 64 96);
      v_9116 <- eval (extract v_9112 32 64);
      v_9117 <- eval (extract v_9112 96 128);
      v_9121 <- eval (isBitSet v_9108 2);
      v_9126 <- eval (isBitSet v_9108 4);
      v_9127 <- getRegister v_3105;
      v_9128 <- eval (extract v_9127 0 32);
      v_9129 <- eval (extract v_9127 64 96);
      v_9131 <- eval (extract v_9127 32 64);
      v_9132 <- eval (extract v_9127 96 128);
      v_9136 <- eval (isBitSet v_9108 6);
      setRegister (lhs.of_reg v_3105) (concat (mux (isBitSet v_9108 1) (mux v_9110 v_9113 v_9114) (mux v_9110 v_9116 v_9117)) (concat (mux (isBitSet v_9108 3) (mux v_9121 v_9113 v_9114) (mux v_9121 v_9116 v_9117)) (concat (mux (isBitSet v_9108 5) (mux v_9126 v_9128 v_9129) (mux v_9126 v_9131 v_9132)) (mux (isBitSet v_9108 7) (mux v_9136 v_9128 v_9129) (mux v_9136 v_9131 v_9132)))));
      pure ()
    pat_end
