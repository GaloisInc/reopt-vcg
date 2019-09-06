def vpermilpd1 : instruction :=
  definst "vpermilpd" $ do
    pattern fun (v_3063 : imm int) (v_3064 : reg (bv 128)) (v_3065 : reg (bv 128)) => do
      v_8183 <- eval (handleImmediateWithSignExtend v_3063 8 8);
      v_8185 <- getRegister v_3064;
      v_8186 <- eval (extract v_8185 64 128);
      v_8187 <- eval (extract v_8185 0 64);
      setRegister (lhs.of_reg v_3065) (concat (mux (isBitClear v_8183 6) v_8186 v_8187) (mux (isBitClear v_8183 7) v_8186 v_8187));
      pure ()
    pat_end;
    pattern fun (v_3074 : reg (bv 128)) (v_3075 : reg (bv 128)) (v_3076 : reg (bv 128)) => do
      v_8198 <- getRegister v_3074;
      v_8200 <- getRegister v_3075;
      v_8201 <- eval (extract v_8200 64 128);
      v_8202 <- eval (extract v_8200 0 64);
      setRegister (lhs.of_reg v_3076) (concat (mux (isBitClear v_8198 62) v_8201 v_8202) (mux (isBitClear v_8198 126) v_8201 v_8202));
      pure ()
    pat_end;
    pattern fun (v_3085 : imm int) (v_3086 : reg (bv 256)) (v_3087 : reg (bv 256)) => do
      v_8213 <- eval (handleImmediateWithSignExtend v_3085 8 8);
      v_8215 <- getRegister v_3086;
      v_8216 <- eval (extract v_8215 64 128);
      v_8217 <- eval (extract v_8215 0 64);
      v_8222 <- eval (extract v_8215 192 256);
      v_8223 <- eval (extract v_8215 128 192);
      setRegister (lhs.of_reg v_3087) (concat (mux (isBitClear v_8213 4) v_8216 v_8217) (concat (mux (isBitClear v_8213 5) v_8216 v_8217) (concat (mux (isBitClear v_8213 6) v_8222 v_8223) (mux (isBitClear v_8213 7) v_8222 v_8223))));
      pure ()
    pat_end;
    pattern fun (v_3096 : reg (bv 256)) (v_3097 : reg (bv 256)) (v_3098 : reg (bv 256)) => do
      v_8236 <- getRegister v_3096;
      v_8238 <- getRegister v_3097;
      v_8239 <- eval (extract v_8238 64 128);
      v_8240 <- eval (extract v_8238 0 64);
      v_8245 <- eval (extract v_8238 192 256);
      v_8246 <- eval (extract v_8238 128 192);
      setRegister (lhs.of_reg v_3098) (concat (mux (isBitClear v_8236 62) v_8239 v_8240) (concat (mux (isBitClear v_8236 126) v_8239 v_8240) (concat (mux (isBitClear v_8236 190) v_8245 v_8246) (mux (isBitClear v_8236 254) v_8245 v_8246))));
      pure ()
    pat_end;
    pattern fun (v_3059 : imm int) (v_3058 : Mem) (v_3060 : reg (bv 128)) => do
      v_16721 <- eval (handleImmediateWithSignExtend v_3059 8 8);
      v_16723 <- evaluateAddress v_3058;
      v_16724 <- load v_16723 16;
      v_16725 <- eval (extract v_16724 64 128);
      v_16726 <- eval (extract v_16724 0 64);
      setRegister (lhs.of_reg v_3060) (concat (mux (isBitClear v_16721 6) v_16725 v_16726) (mux (isBitClear v_16721 7) v_16725 v_16726));
      pure ()
    pat_end;
    pattern fun (v_3069 : Mem) (v_3070 : reg (bv 128)) (v_3071 : reg (bv 128)) => do
      v_16732 <- evaluateAddress v_3069;
      v_16733 <- load v_16732 16;
      v_16735 <- getRegister v_3070;
      v_16736 <- eval (extract v_16735 64 128);
      v_16737 <- eval (extract v_16735 0 64);
      setRegister (lhs.of_reg v_3071) (concat (mux (isBitClear v_16733 62) v_16736 v_16737) (mux (isBitClear v_16733 126) v_16736 v_16737));
      pure ()
    pat_end;
    pattern fun (v_3081 : imm int) (v_3080 : Mem) (v_3082 : reg (bv 256)) => do
      v_16743 <- eval (handleImmediateWithSignExtend v_3081 8 8);
      v_16745 <- evaluateAddress v_3080;
      v_16746 <- load v_16745 32;
      v_16747 <- eval (extract v_16746 64 128);
      v_16748 <- eval (extract v_16746 0 64);
      v_16753 <- eval (extract v_16746 192 256);
      v_16754 <- eval (extract v_16746 128 192);
      setRegister (lhs.of_reg v_3082) (concat (mux (isBitClear v_16743 4) v_16747 v_16748) (concat (mux (isBitClear v_16743 5) v_16747 v_16748) (concat (mux (isBitClear v_16743 6) v_16753 v_16754) (mux (isBitClear v_16743 7) v_16753 v_16754))));
      pure ()
    pat_end;
    pattern fun (v_3091 : Mem) (v_3092 : reg (bv 256)) (v_3093 : reg (bv 256)) => do
      v_16762 <- evaluateAddress v_3091;
      v_16763 <- load v_16762 32;
      v_16765 <- getRegister v_3092;
      v_16766 <- eval (extract v_16765 64 128);
      v_16767 <- eval (extract v_16765 0 64);
      v_16772 <- eval (extract v_16765 192 256);
      v_16773 <- eval (extract v_16765 128 192);
      setRegister (lhs.of_reg v_3093) (concat (mux (isBitClear v_16763 62) v_16766 v_16767) (concat (mux (isBitClear v_16763 126) v_16766 v_16767) (concat (mux (isBitClear v_16763 190) v_16772 v_16773) (mux (isBitClear v_16763 254) v_16772 v_16773))));
      pure ()
    pat_end
