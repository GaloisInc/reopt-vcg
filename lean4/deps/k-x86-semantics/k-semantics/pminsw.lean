def pminsw1 : instruction :=
  definst "pminsw" $ do
    pattern fun (v_2711 : reg (bv 128)) (v_2712 : reg (bv 128)) => do
      v_5187 <- getRegister v_2712;
      v_5188 <- eval (extract v_5187 0 16);
      v_5189 <- getRegister v_2711;
      v_5190 <- eval (extract v_5189 0 16);
      v_5193 <- eval (extract v_5187 16 32);
      v_5194 <- eval (extract v_5189 16 32);
      v_5197 <- eval (extract v_5187 32 48);
      v_5198 <- eval (extract v_5189 32 48);
      v_5201 <- eval (extract v_5187 48 64);
      v_5202 <- eval (extract v_5189 48 64);
      v_5205 <- eval (extract v_5187 64 80);
      v_5206 <- eval (extract v_5189 64 80);
      v_5209 <- eval (extract v_5187 80 96);
      v_5210 <- eval (extract v_5189 80 96);
      v_5213 <- eval (extract v_5187 96 112);
      v_5214 <- eval (extract v_5189 96 112);
      v_5217 <- eval (extract v_5187 112 128);
      v_5218 <- eval (extract v_5189 112 128);
      setRegister (lhs.of_reg v_2712) (concat (mux (slt v_5188 v_5190) v_5188 v_5190) (concat (mux (slt v_5193 v_5194) v_5193 v_5194) (concat (mux (slt v_5197 v_5198) v_5197 v_5198) (concat (mux (slt v_5201 v_5202) v_5201 v_5202) (concat (mux (slt v_5205 v_5206) v_5205 v_5206) (concat (mux (slt v_5209 v_5210) v_5209 v_5210) (concat (mux (slt v_5213 v_5214) v_5213 v_5214) (mux (slt v_5217 v_5218) v_5217 v_5218))))))));
      pure ()
    pat_end;
    pattern fun (v_2707 : Mem) (v_2708 : reg (bv 128)) => do
      v_12016 <- getRegister v_2708;
      v_12017 <- eval (extract v_12016 0 16);
      v_12018 <- evaluateAddress v_2707;
      v_12019 <- load v_12018 16;
      v_12020 <- eval (extract v_12019 0 16);
      v_12023 <- eval (extract v_12016 16 32);
      v_12024 <- eval (extract v_12019 16 32);
      v_12027 <- eval (extract v_12016 32 48);
      v_12028 <- eval (extract v_12019 32 48);
      v_12031 <- eval (extract v_12016 48 64);
      v_12032 <- eval (extract v_12019 48 64);
      v_12035 <- eval (extract v_12016 64 80);
      v_12036 <- eval (extract v_12019 64 80);
      v_12039 <- eval (extract v_12016 80 96);
      v_12040 <- eval (extract v_12019 80 96);
      v_12043 <- eval (extract v_12016 96 112);
      v_12044 <- eval (extract v_12019 96 112);
      v_12047 <- eval (extract v_12016 112 128);
      v_12048 <- eval (extract v_12019 112 128);
      setRegister (lhs.of_reg v_2708) (concat (mux (slt v_12017 v_12020) v_12017 v_12020) (concat (mux (slt v_12023 v_12024) v_12023 v_12024) (concat (mux (slt v_12027 v_12028) v_12027 v_12028) (concat (mux (slt v_12031 v_12032) v_12031 v_12032) (concat (mux (slt v_12035 v_12036) v_12035 v_12036) (concat (mux (slt v_12039 v_12040) v_12039 v_12040) (concat (mux (slt v_12043 v_12044) v_12043 v_12044) (mux (slt v_12047 v_12048) v_12047 v_12048))))))));
      pure ()
    pat_end
