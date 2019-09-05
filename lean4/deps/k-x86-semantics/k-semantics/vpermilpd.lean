def vpermilpd1 : instruction :=
  definst "vpermilpd" $ do
    pattern fun (v_3036 : imm int) (v_3038 : reg (bv 128)) (v_3039 : reg (bv 128)) => do
      v_8156 <- eval (handleImmediateWithSignExtend v_3036 8 8);
      v_8158 <- getRegister v_3038;
      v_8159 <- eval (extract v_8158 64 128);
      v_8160 <- eval (extract v_8158 0 64);
      setRegister (lhs.of_reg v_3039) (concat (mux (isBitClear v_8156 6) v_8159 v_8160) (mux (isBitClear v_8156 7) v_8159 v_8160));
      pure ()
    pat_end;
    pattern fun (v_3048 : reg (bv 128)) (v_3049 : reg (bv 128)) (v_3050 : reg (bv 128)) => do
      v_8171 <- getRegister v_3048;
      v_8173 <- getRegister v_3049;
      v_8174 <- eval (extract v_8173 64 128);
      v_8175 <- eval (extract v_8173 0 64);
      setRegister (lhs.of_reg v_3050) (concat (mux (isBitClear v_8171 62) v_8174 v_8175) (mux (isBitClear v_8171 126) v_8174 v_8175));
      pure ()
    pat_end;
    pattern fun (v_3058 : imm int) (v_3059 : reg (bv 256)) (v_3060 : reg (bv 256)) => do
      v_8186 <- eval (handleImmediateWithSignExtend v_3058 8 8);
      v_8188 <- getRegister v_3059;
      v_8189 <- eval (extract v_8188 64 128);
      v_8190 <- eval (extract v_8188 0 64);
      v_8195 <- eval (extract v_8188 192 256);
      v_8196 <- eval (extract v_8188 128 192);
      setRegister (lhs.of_reg v_3060) (concat (mux (isBitClear v_8186 4) v_8189 v_8190) (concat (mux (isBitClear v_8186 5) v_8189 v_8190) (concat (mux (isBitClear v_8186 6) v_8195 v_8196) (mux (isBitClear v_8186 7) v_8195 v_8196))));
      pure ()
    pat_end;
    pattern fun (v_3069 : reg (bv 256)) (v_3070 : reg (bv 256)) (v_3071 : reg (bv 256)) => do
      v_8209 <- getRegister v_3069;
      v_8211 <- getRegister v_3070;
      v_8212 <- eval (extract v_8211 64 128);
      v_8213 <- eval (extract v_8211 0 64);
      v_8218 <- eval (extract v_8211 192 256);
      v_8219 <- eval (extract v_8211 128 192);
      setRegister (lhs.of_reg v_3071) (concat (mux (isBitClear v_8209 62) v_8212 v_8213) (concat (mux (isBitClear v_8209 126) v_8212 v_8213) (concat (mux (isBitClear v_8209 190) v_8218 v_8219) (mux (isBitClear v_8209 254) v_8218 v_8219))));
      pure ()
    pat_end;
    pattern fun (v_3031 : imm int) (v_3032 : Mem) (v_3033 : reg (bv 128)) => do
      v_16694 <- eval (handleImmediateWithSignExtend v_3031 8 8);
      v_16696 <- evaluateAddress v_3032;
      v_16697 <- load v_16696 16;
      v_16698 <- eval (extract v_16697 64 128);
      v_16699 <- eval (extract v_16697 0 64);
      setRegister (lhs.of_reg v_3033) (concat (mux (isBitClear v_16694 6) v_16698 v_16699) (mux (isBitClear v_16694 7) v_16698 v_16699));
      pure ()
    pat_end;
    pattern fun (v_3042 : Mem) (v_3043 : reg (bv 128)) (v_3044 : reg (bv 128)) => do
      v_16705 <- evaluateAddress v_3042;
      v_16706 <- load v_16705 16;
      v_16708 <- getRegister v_3043;
      v_16709 <- eval (extract v_16708 64 128);
      v_16710 <- eval (extract v_16708 0 64);
      setRegister (lhs.of_reg v_3044) (concat (mux (isBitClear v_16706 62) v_16709 v_16710) (mux (isBitClear v_16706 126) v_16709 v_16710));
      pure ()
    pat_end;
    pattern fun (v_3053 : imm int) (v_3054 : Mem) (v_3055 : reg (bv 256)) => do
      v_16716 <- eval (handleImmediateWithSignExtend v_3053 8 8);
      v_16718 <- evaluateAddress v_3054;
      v_16719 <- load v_16718 32;
      v_16720 <- eval (extract v_16719 64 128);
      v_16721 <- eval (extract v_16719 0 64);
      v_16726 <- eval (extract v_16719 192 256);
      v_16727 <- eval (extract v_16719 128 192);
      setRegister (lhs.of_reg v_3055) (concat (mux (isBitClear v_16716 4) v_16720 v_16721) (concat (mux (isBitClear v_16716 5) v_16720 v_16721) (concat (mux (isBitClear v_16716 6) v_16726 v_16727) (mux (isBitClear v_16716 7) v_16726 v_16727))));
      pure ()
    pat_end;
    pattern fun (v_3064 : Mem) (v_3065 : reg (bv 256)) (v_3066 : reg (bv 256)) => do
      v_16735 <- evaluateAddress v_3064;
      v_16736 <- load v_16735 32;
      v_16738 <- getRegister v_3065;
      v_16739 <- eval (extract v_16738 64 128);
      v_16740 <- eval (extract v_16738 0 64);
      v_16745 <- eval (extract v_16738 192 256);
      v_16746 <- eval (extract v_16738 128 192);
      setRegister (lhs.of_reg v_3066) (concat (mux (isBitClear v_16736 62) v_16739 v_16740) (concat (mux (isBitClear v_16736 126) v_16739 v_16740) (concat (mux (isBitClear v_16736 190) v_16745 v_16746) (mux (isBitClear v_16736 254) v_16745 v_16746))));
      pure ()
    pat_end
