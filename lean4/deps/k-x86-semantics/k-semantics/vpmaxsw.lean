def vpmaxsw1 : instruction :=
  definst "vpmaxsw" $ do
    pattern fun (v_3561 : reg (bv 128)) (v_3562 : reg (bv 128)) (v_3563 : reg (bv 128)) => do
      v_10714 <- getRegister v_3562;
      v_10715 <- eval (extract v_10714 0 16);
      v_10716 <- getRegister v_3561;
      v_10717 <- eval (extract v_10716 0 16);
      v_10720 <- eval (extract v_10714 16 32);
      v_10721 <- eval (extract v_10716 16 32);
      v_10724 <- eval (extract v_10714 32 48);
      v_10725 <- eval (extract v_10716 32 48);
      v_10728 <- eval (extract v_10714 48 64);
      v_10729 <- eval (extract v_10716 48 64);
      v_10732 <- eval (extract v_10714 64 80);
      v_10733 <- eval (extract v_10716 64 80);
      v_10736 <- eval (extract v_10714 80 96);
      v_10737 <- eval (extract v_10716 80 96);
      v_10740 <- eval (extract v_10714 96 112);
      v_10741 <- eval (extract v_10716 96 112);
      v_10744 <- eval (extract v_10714 112 128);
      v_10745 <- eval (extract v_10716 112 128);
      setRegister (lhs.of_reg v_3563) (concat (mux (sgt v_10715 v_10717) v_10715 v_10717) (concat (mux (sgt v_10720 v_10721) v_10720 v_10721) (concat (mux (sgt v_10724 v_10725) v_10724 v_10725) (concat (mux (sgt v_10728 v_10729) v_10728 v_10729) (concat (mux (sgt v_10732 v_10733) v_10732 v_10733) (concat (mux (sgt v_10736 v_10737) v_10736 v_10737) (concat (mux (sgt v_10740 v_10741) v_10740 v_10741) (mux (sgt v_10744 v_10745) v_10744 v_10745))))))));
      pure ()
    pat_end;
    pattern fun (v_3572 : reg (bv 256)) (v_3573 : reg (bv 256)) (v_3574 : reg (bv 256)) => do
      v_10761 <- getRegister v_3573;
      v_10762 <- eval (extract v_10761 0 16);
      v_10763 <- getRegister v_3572;
      v_10764 <- eval (extract v_10763 0 16);
      v_10767 <- eval (extract v_10761 16 32);
      v_10768 <- eval (extract v_10763 16 32);
      v_10771 <- eval (extract v_10761 32 48);
      v_10772 <- eval (extract v_10763 32 48);
      v_10775 <- eval (extract v_10761 48 64);
      v_10776 <- eval (extract v_10763 48 64);
      v_10779 <- eval (extract v_10761 64 80);
      v_10780 <- eval (extract v_10763 64 80);
      v_10783 <- eval (extract v_10761 80 96);
      v_10784 <- eval (extract v_10763 80 96);
      v_10787 <- eval (extract v_10761 96 112);
      v_10788 <- eval (extract v_10763 96 112);
      v_10791 <- eval (extract v_10761 112 128);
      v_10792 <- eval (extract v_10763 112 128);
      v_10795 <- eval (extract v_10761 128 144);
      v_10796 <- eval (extract v_10763 128 144);
      v_10799 <- eval (extract v_10761 144 160);
      v_10800 <- eval (extract v_10763 144 160);
      v_10803 <- eval (extract v_10761 160 176);
      v_10804 <- eval (extract v_10763 160 176);
      v_10807 <- eval (extract v_10761 176 192);
      v_10808 <- eval (extract v_10763 176 192);
      v_10811 <- eval (extract v_10761 192 208);
      v_10812 <- eval (extract v_10763 192 208);
      v_10815 <- eval (extract v_10761 208 224);
      v_10816 <- eval (extract v_10763 208 224);
      v_10819 <- eval (extract v_10761 224 240);
      v_10820 <- eval (extract v_10763 224 240);
      v_10823 <- eval (extract v_10761 240 256);
      v_10824 <- eval (extract v_10763 240 256);
      setRegister (lhs.of_reg v_3574) (concat (mux (sgt v_10762 v_10764) v_10762 v_10764) (concat (mux (sgt v_10767 v_10768) v_10767 v_10768) (concat (mux (sgt v_10771 v_10772) v_10771 v_10772) (concat (mux (sgt v_10775 v_10776) v_10775 v_10776) (concat (mux (sgt v_10779 v_10780) v_10779 v_10780) (concat (mux (sgt v_10783 v_10784) v_10783 v_10784) (concat (mux (sgt v_10787 v_10788) v_10787 v_10788) (concat (mux (sgt v_10791 v_10792) v_10791 v_10792) (concat (mux (sgt v_10795 v_10796) v_10795 v_10796) (concat (mux (sgt v_10799 v_10800) v_10799 v_10800) (concat (mux (sgt v_10803 v_10804) v_10803 v_10804) (concat (mux (sgt v_10807 v_10808) v_10807 v_10808) (concat (mux (sgt v_10811 v_10812) v_10811 v_10812) (concat (mux (sgt v_10815 v_10816) v_10815 v_10816) (concat (mux (sgt v_10819 v_10820) v_10819 v_10820) (mux (sgt v_10823 v_10824) v_10823 v_10824))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_3556 : Mem) (v_3557 : reg (bv 128)) (v_3558 : reg (bv 128)) => do
      v_19079 <- getRegister v_3557;
      v_19080 <- eval (extract v_19079 0 16);
      v_19081 <- evaluateAddress v_3556;
      v_19082 <- load v_19081 16;
      v_19083 <- eval (extract v_19082 0 16);
      v_19086 <- eval (extract v_19079 16 32);
      v_19087 <- eval (extract v_19082 16 32);
      v_19090 <- eval (extract v_19079 32 48);
      v_19091 <- eval (extract v_19082 32 48);
      v_19094 <- eval (extract v_19079 48 64);
      v_19095 <- eval (extract v_19082 48 64);
      v_19098 <- eval (extract v_19079 64 80);
      v_19099 <- eval (extract v_19082 64 80);
      v_19102 <- eval (extract v_19079 80 96);
      v_19103 <- eval (extract v_19082 80 96);
      v_19106 <- eval (extract v_19079 96 112);
      v_19107 <- eval (extract v_19082 96 112);
      v_19110 <- eval (extract v_19079 112 128);
      v_19111 <- eval (extract v_19082 112 128);
      setRegister (lhs.of_reg v_3558) (concat (mux (sgt v_19080 v_19083) v_19080 v_19083) (concat (mux (sgt v_19086 v_19087) v_19086 v_19087) (concat (mux (sgt v_19090 v_19091) v_19090 v_19091) (concat (mux (sgt v_19094 v_19095) v_19094 v_19095) (concat (mux (sgt v_19098 v_19099) v_19098 v_19099) (concat (mux (sgt v_19102 v_19103) v_19102 v_19103) (concat (mux (sgt v_19106 v_19107) v_19106 v_19107) (mux (sgt v_19110 v_19111) v_19110 v_19111))))))));
      pure ()
    pat_end;
    pattern fun (v_3567 : Mem) (v_3568 : reg (bv 256)) (v_3569 : reg (bv 256)) => do
      v_19122 <- getRegister v_3568;
      v_19123 <- eval (extract v_19122 0 16);
      v_19124 <- evaluateAddress v_3567;
      v_19125 <- load v_19124 32;
      v_19126 <- eval (extract v_19125 0 16);
      v_19129 <- eval (extract v_19122 16 32);
      v_19130 <- eval (extract v_19125 16 32);
      v_19133 <- eval (extract v_19122 32 48);
      v_19134 <- eval (extract v_19125 32 48);
      v_19137 <- eval (extract v_19122 48 64);
      v_19138 <- eval (extract v_19125 48 64);
      v_19141 <- eval (extract v_19122 64 80);
      v_19142 <- eval (extract v_19125 64 80);
      v_19145 <- eval (extract v_19122 80 96);
      v_19146 <- eval (extract v_19125 80 96);
      v_19149 <- eval (extract v_19122 96 112);
      v_19150 <- eval (extract v_19125 96 112);
      v_19153 <- eval (extract v_19122 112 128);
      v_19154 <- eval (extract v_19125 112 128);
      v_19157 <- eval (extract v_19122 128 144);
      v_19158 <- eval (extract v_19125 128 144);
      v_19161 <- eval (extract v_19122 144 160);
      v_19162 <- eval (extract v_19125 144 160);
      v_19165 <- eval (extract v_19122 160 176);
      v_19166 <- eval (extract v_19125 160 176);
      v_19169 <- eval (extract v_19122 176 192);
      v_19170 <- eval (extract v_19125 176 192);
      v_19173 <- eval (extract v_19122 192 208);
      v_19174 <- eval (extract v_19125 192 208);
      v_19177 <- eval (extract v_19122 208 224);
      v_19178 <- eval (extract v_19125 208 224);
      v_19181 <- eval (extract v_19122 224 240);
      v_19182 <- eval (extract v_19125 224 240);
      v_19185 <- eval (extract v_19122 240 256);
      v_19186 <- eval (extract v_19125 240 256);
      setRegister (lhs.of_reg v_3569) (concat (mux (sgt v_19123 v_19126) v_19123 v_19126) (concat (mux (sgt v_19129 v_19130) v_19129 v_19130) (concat (mux (sgt v_19133 v_19134) v_19133 v_19134) (concat (mux (sgt v_19137 v_19138) v_19137 v_19138) (concat (mux (sgt v_19141 v_19142) v_19141 v_19142) (concat (mux (sgt v_19145 v_19146) v_19145 v_19146) (concat (mux (sgt v_19149 v_19150) v_19149 v_19150) (concat (mux (sgt v_19153 v_19154) v_19153 v_19154) (concat (mux (sgt v_19157 v_19158) v_19157 v_19158) (concat (mux (sgt v_19161 v_19162) v_19161 v_19162) (concat (mux (sgt v_19165 v_19166) v_19165 v_19166) (concat (mux (sgt v_19169 v_19170) v_19169 v_19170) (concat (mux (sgt v_19173 v_19174) v_19173 v_19174) (concat (mux (sgt v_19177 v_19178) v_19177 v_19178) (concat (mux (sgt v_19181 v_19182) v_19181 v_19182) (mux (sgt v_19185 v_19186) v_19185 v_19186))))))))))))))));
      pure ()
    pat_end
